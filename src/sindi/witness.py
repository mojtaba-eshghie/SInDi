# src/sindi/witness.py
import sympy as sp
import z3
from dataclasses import dataclass, field
from typing import Literal, Any, Dict, List, Optional
import re

@dataclass
class DomainSpec:
    """Specifies the domain for a variable in the witness solver."""
    kind: Literal["uint", "int", "bool", "address", "real"]
    bits: int | None = None   # e.g. 256 for uint/int, 160 for address
    min: int | None = None
    max: int | None = None

@dataclass
class WitnessResult:
    """Result of a witness query."""
    sat: bool | None                 # True/SAT, False/UNSAT, None/UNKNOWN/ERROR
    model: Dict[str, Any] = field(default_factory=dict) # symbol -> python value
    unconstrained: List[str] = field(default_factory=list)
    z3_formula: str = ""
    simplified_new: str = ""
    simplified_old: str = ""
    error: str | None = None

class WitnessSolver:
    """
    Solver engine for finding counter-examples (witnesses) where:
    new_pred is TRUE and old_pred is FALSE.
    """
    
    def __init__(self, comparator):
        # We hold a reference to the comparator to reuse its parsing/rewriting pipeline
        self.comp = comparator

    def solve(
        self,
        new_pred: str,
        old_pred: str,
        *,
        domains: Dict[str, DomainSpec] | None = None,
        simplify: bool = True,
    ) -> WitnessResult:
        try:
            # 1. Parse & Normalize using the centralized Comparator pipeline
            new_ast = self.comp._parse_predicate(new_pred)
            old_ast = self.comp._parse_predicate(old_pred)

            # 2. Convert to SymPy
            new_expr = self.comp._to_sympy_expr(new_ast)
            old_expr = self.comp._to_sympy_expr(old_ast)

            # 3. Simplify (optional but recommended for cleaner Z3 exprs)
            if simplify:
                new_expr = sp.simplify(new_expr)
                old_expr = sp.simplify(old_expr)

            # 4. Formulate: New AND (NOT Old)
            formula = sp.And(new_expr, sp.Not(old_expr))
            
            # optional: simplify formula again to catch trivial True/False early
            if simplify:
                formula = sp.simplify(formula)

            # 5. Infer Sorts (Bool vs Real)
            sorts = self._infer_symbol_sorts(formula, domains)

            # 6. Build Z3 Environment
            z3_env = {}
            for name, sort_type in sorts.items():
                if sort_type == "Bool":
                    z3_env[name] = z3.Bool(name)
                else:
                    z3_env[name] = z3.Real(name)

            # 7. Translate to Z3
            try:
                z3_formula = self._sympy_to_z3_typed(formula, z3_env, sorts)
            except Exception as e:
                return WitnessResult(
                    sat=None, 
                    error=f"Translation failed: {e}",
                    simplified_new=str(new_expr),
                    simplified_old=str(old_expr)
                )

            # 8. Setup Solver and Constraints
            s = z3.Solver()
            s.add(z3_formula)
            self._add_domain_constraints(s, z3_env, sorts, domains)

            # 9. Check
            check_res = s.check()

            if check_res == z3.sat:
                m = s.model()
                model_dict, unconstrained = self._extract_model(m, z3_env, sorts)
                return WitnessResult(
                    sat=True,
                    model=model_dict,
                    unconstrained=unconstrained,
                    z3_formula=str(z3_formula),
                    simplified_new=str(new_expr),
                    simplified_old=str(old_expr)
                )
            elif check_res == z3.unsat:
                return WitnessResult(
                    sat=False,
                    z3_formula=str(z3_formula),
                    simplified_new=str(new_expr),
                    simplified_old=str(old_expr)
                )
            else:
                return WitnessResult(
                    sat=None,
                    error=f"Z3 returned unknown: {s.reason_unknown()}",
                    z3_formula=str(z3_formula),
                    simplified_new=str(new_expr),
                    simplified_old=str(old_expr)
                )

        except Exception as e:
            return WitnessResult(sat=None, error=str(e))

    def _infer_symbol_sorts(self, expr: sp.Expr, domains: Dict[str, DomainSpec] | None) -> Dict[str, str]:
        """
        Traverses the SymPy expression to deduce if a symbol is treated as Boolean
        (inside And/Or/Not) or Numeric (inside Gt/Lt/Add/Mul).
        """
        sorts = {}
        
        # Pre-fill from explicitly provided domains
        if domains:
            for name, spec in domains.items():
                if spec.kind == 'bool':
                    sorts[name] = "Bool"
                else:
                    sorts[name] = "Real"

        def set_sort(name, sort_type):
            if name in sorts and sorts[name] != sort_type:
                pass 
            if name not in sorts:
                sorts[name] = sort_type

        def visit(node, expected_ctx: str):
            if isinstance(node, sp.Symbol):
                set_sort(str(node), expected_ctx)
                return

            # Boolean Logical Operators -> Require Children to be Bool
            if isinstance(node, (sp.And, sp.Or, sp.Not)):
                for arg in node.args:
                    visit(arg, "Bool")
            
            # Numeric Operators -> Require Children to be Real
            elif isinstance(node, (sp.Add, sp.Mul, sp.Pow)):
                for arg in node.args:
                    visit(arg, "Real")

            # Relational Operators (Gt, Lt...) -> Children are Real
            elif isinstance(node, (sp.Gt, sp.Lt, sp.Ge, sp.Le)):
                for arg in node.args:
                    visit(arg, "Real")

            # Equality/Inequality (Eq, Ne)
            elif isinstance(node, (sp.Eq, sp.Ne)):
                is_bool_eq = any((arg is sp.true or arg is sp.false) for arg in node.args)
                target = "Bool" if is_bool_eq else "Real"
                for arg in node.args:
                    if arg is not sp.true and arg is not sp.false:
                        visit(arg, target)
            
            # Functions (calls) -> treat as atomic symbols based on context
            elif isinstance(node, sp.Function):
                set_sort(str(node).replace("(", "").replace(")", ""), expected_ctx)

        visit(expr, "Bool")

        # Fallback for unvisited symbols
        for sym in expr.free_symbols:
            s_name = str(sym)
            if s_name not in sorts:
                sorts[s_name] = "Real"
        
        return sorts

    def _sympy_to_z3_typed(self, expr, z3_env, sorts):
        """
        Recursive translation that handles both Bool and Real sorts.
        """
        # Handle Boolean Literals (True/False) explicitly
        if expr is sp.true: 
            return True
        if expr is sp.false: 
            return False
        
        # Also catch SymPy BooleanAtom types (singleton subclasses)
        if isinstance(expr, sp.logic.boolalg.BooleanAtom):
             return bool(expr)

        if isinstance(expr, sp.Symbol):
            return z3_env[str(expr)]
        
        elif isinstance(expr, sp.Number):
            if expr.is_Integer:
                return float(expr) 
            return float(expr)

        elif isinstance(expr, sp.Function):
            func_name = str(expr).replace('[', '_').replace(']', '').replace('.', '_')
            return z3_env.get(func_name, z3.Real(func_name))

        # Logical
        if isinstance(expr, sp.And):
            return z3.And(*[self._sympy_to_z3_typed(a, z3_env, sorts) for a in expr.args])
        if isinstance(expr, sp.Or):
            return z3.Or(*[self._sympy_to_z3_typed(a, z3_env, sorts) for a in expr.args])
        if isinstance(expr, sp.Not):
            return z3.Not(self._sympy_to_z3_typed(expr.args[0], z3_env, sorts))
        
        # Relational
        if isinstance(expr, sp.Eq):
            return self._sympy_to_z3_typed(expr.lhs, z3_env, sorts) == self._sympy_to_z3_typed(expr.rhs, z3_env, sorts)
        if isinstance(expr, sp.Ne):
            return self._sympy_to_z3_typed(expr.lhs, z3_env, sorts) != self._sympy_to_z3_typed(expr.rhs, z3_env, sorts)
        if isinstance(expr, sp.Gt):
            return self._sympy_to_z3_typed(expr.lhs, z3_env, sorts) > self._sympy_to_z3_typed(expr.rhs, z3_env, sorts)
        if isinstance(expr, sp.Ge):
            return self._sympy_to_z3_typed(expr.lhs, z3_env, sorts) >= self._sympy_to_z3_typed(expr.rhs, z3_env, sorts)
        if isinstance(expr, sp.Lt):
            return self._sympy_to_z3_typed(expr.lhs, z3_env, sorts) < self._sympy_to_z3_typed(expr.rhs, z3_env, sorts)
        if isinstance(expr, sp.Le):
            return self._sympy_to_z3_typed(expr.lhs, z3_env, sorts) <= self._sympy_to_z3_typed(expr.rhs, z3_env, sorts)

        # Arithmetic
        if isinstance(expr, sp.Add):
            return z3.Sum(*[self._sympy_to_z3_typed(a, z3_env, sorts) for a in expr.args])
        if isinstance(expr, sp.Mul):
            res = self._sympy_to_z3_typed(expr.args[0], z3_env, sorts)
            for a in expr.args[1:]:
                res = res * self._sympy_to_z3_typed(a, z3_env, sorts)
            return res
        if isinstance(expr, sp.Pow):
            return self._sympy_to_z3_typed(expr.args[0], z3_env, sorts) ** self._sympy_to_z3_typed(expr.args[1], z3_env, sorts)

        raise ValueError(f"Unsupported expression type in typed translation: {type(expr)} - {expr}")

    def _add_domain_constraints(self, s: z3.Solver, z3_env, sorts, domains):
        """
        Applies domain constraints (non-negativity or bit limits).
        """
        for name, z3_var in z3_env.items():
            if domains and name in domains:
                spec = domains[name]
                if spec.kind == 'uint' or spec.kind == 'address':
                    s.add(z3_var >= 0)
                    bits = spec.bits if spec.bits else (160 if spec.kind == 'address' else 256)
                    s.add(z3_var <= (2**bits) - 1)
                elif spec.kind == 'int':
                    bits = spec.bits if spec.bits else 256
                    limit = 2**(bits-1)
                    s.add(z3_var >= -limit)
                    s.add(z3_var <= limit - 1)
                if spec.min is not None: s.add(z3_var >= spec.min)
                if spec.max is not None: s.add(z3_var <= spec.max)
            
            elif sorts[name] == "Real":
                s.add(z3_var >= 0)

    def _extract_model(self, model, z3_env, sorts):
        results = {}
        unconstrained = []
        
        for name, z3_var in z3_env.items():
            val_ref = model.eval(z3_var, model_completion=True)
            
            if sorts[name] == "Bool":
                results[name] = bool(z3.is_true(val_ref))
            else:
                if hasattr(val_ref, 'is_int') and val_ref.is_int():
                    results[name] = int(val_ref.as_string())
                elif hasattr(val_ref, 'numerator_as_long'):
                    num = val_ref.numerator_as_long()
                    den = val_ref.denominator_as_long()
                    if den == 1:
                        results[name] = num
                    else:
                        results[name] = float(num) / float(den)
                else:
                    try:
                        results[name] = float(val_ref.as_decimal(10).replace('?',''))
                    except:
                        results[name] = str(val_ref)

        return results, unconstrained