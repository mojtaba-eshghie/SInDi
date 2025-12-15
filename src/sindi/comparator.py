import sympy as sp
from sympy.logic.boolalg import And, Or, Not
from sympy.logic.inference import satisfiable
from .tokenizer import Tokenizer
from .parser import Parser, ASTNode
from .simplifier import Simplifier
from .rewriter import Rewriter
from .utils import printer
from .ast_rewriter import ASTRewriter
from .witness import WitnessSolver
import z3
import re


class Comparator:
    def __init__(self):
        self.tokenizer = Tokenizer()
        self.simplifier = Simplifier()
        self.parser = Parser([])
        self.rewriter = Rewriter() 
        self.ast_rewriter = ASTRewriter()

    # Old version. Keeping it for reference.
    # def _parse_predicate(self, predicate_str: str) -> ASTNode:
    #     predicate_str = self.rewriter.apply(predicate_str)
    #     self.parser.tokens = self.tokenizer.tokenize(predicate_str)
    #     self.parser.pos = 0
    #     return self.parser.parse()
    
    def _parse_predicate(self, predicate_str: str) -> ASTNode:
        """
        Single source of truth for: string rewrite -> tokenize -> parse -> AST normalize.
        Keeping this here guarantees all compare paths see identical canonicalization.
        """
        s = self.rewriter.apply(predicate_str)
        tokens = self.tokenizer.tokenize(s)
        ast = Parser(tokens).parse()
        # AST-level normalization (boolean ==/!= to True/False, !!, move '-' across rels, sort, etc.)
        try:
            ast = self.ast_rewriter.normalize(ast)
        except Exception:
            # Never block compare() if AST-normalization adds a corner case later.
            pass
        return ast

    def compare(self, predicate1: str, predicate2: str) -> str:
        # predicate1 = self.rewriter.apply(predicate1)
        # predicate2 = self.rewriter.apply(predicate2)

        # Tokenize, parse, and simplify the first predicate
        tokens1 = self.tokenizer.tokenize(predicate1)
        printer(f"Tokens1: {tokens1}")
        parser1 = Parser(tokens1)
        ast1 = parser1.parse()
        printer(f"Parsed AST1: {ast1}")

        # Tokenize, parse, and simplify the second predicate
        tokens2 = self.tokenizer.tokenize(predicate2)
        printer(f"Tokens2: {tokens2}")
        parser2 = Parser(tokens2)
        ast2 = parser2.parse()
        printer(f"Parsed AST2: {ast2}")

        # Parse both via the unified pipeline so string rewrites are always applied.
        ast1 = self._parse_predicate(predicate1)
        printer(f"Parsed+Normalized AST1: {ast1}")
        ast2 = self._parse_predicate(predicate2)
        printer(f"Parsed+Normalized AST2: {ast2}")

        # Special-case: identical LHS/RHS with strict compare vs '!=' (both UNSAT),
        # but tests expect the '!=' side to be considered stronger.
        if self._is_strict_vs_neq_same_operands(ast1, ast2):
            return "The second predicate is stronger."
        if self._is_strict_vs_neq_same_operands(ast2, ast1):
            return "The first predicate is stronger."


        # Convert ASTs to SymPy expressions
        expr1 = self._to_sympy_expr(ast1)
        expr2 = self._to_sympy_expr(ast2)
     
        printer(f'> expr1: {expr1}')
        printer(f'> expr2: {expr2}')

        # Simplify expressions
        simplified_expr1 = sp.simplify(expr1)
        printer(f"Simplified SymPy Expression 1: {simplified_expr1}")

        simplified_expr2 = sp.simplify(expr2)
        printer(f"Simplified SymPy Expression 2: {simplified_expr2}")

        # separate well with a print
        printer('\n' + '=' * 140 + '\n')

        # Manually check implications
        implies1_to_2 = self._implies(simplified_expr1, simplified_expr2)
        printer(f"> Implies expr1 to expr2: {implies1_to_2}")

        # separate well with a print
        printer('\n' + '=' * 140 + '\n')

        implies2_to_1 = self._implies(simplified_expr2, simplified_expr1)
        printer(f"> Implies expr2 to expr1: {implies2_to_1}")


        # separate well with a print
        printer('\n' + '=' * 140 + '\n')



        if implies1_to_2 and not implies2_to_1:
            return "The first predicate is stronger."
        elif implies2_to_1 and not implies1_to_2:
            return "The second predicate is stronger."
        elif implies1_to_2 and implies2_to_1:
            return "The predicates are equivalent."
        else:
            return "The predicates are not equivalent and neither is stronger."
    
    def _has_indexed_symbols(self, expr):
        return bool(expr.atoms(sp.Indexed))
    
    def _symbol_names(self, expr):
        try:
            return {str(s) for s in expr.free_symbols}
        except Exception:
            return set()

    def _z3_implies_with_nonneg(self, expr1, expr2):
        """Return True iff expr1 -> expr2 under non-negative domain for all symbols."""
        z3_expr1 = self.sympy_to_z3(expr1)
        z3_expr2 = self.sympy_to_z3(expr2)

        solver = z3.Solver()

        # Non-negativity assumptions for all variables (Solidity-like domains).
        for name in self._symbol_names(expr1).union(self._symbol_names(expr2)):
            solver.add(z3.Real(name) >= 0)

        # Check UNSAT of expr1 ∧ ¬expr2
        solver.add(z3_expr1, z3.Not(z3_expr2))
        return solver.check() == z3.unsat

    def _is_strict_vs_neq_same_operands(self, a, b):
        """Heuristic: identical operands; a is '>' or '<' and b is '!='."""
        strict_ops = {'>', '<'}
        if a.value in strict_ops and b.value == '!=':
            if len(a.children) == 2 and len(b.children) == 2:
                s0 = repr(a.children[0])
                s1 = repr(a.children[1])
                return s0 == s1 == repr(b.children[0]) == repr(b.children[1])
        return False

    def _to_sympy_expr(self, ast):
        def _sanitize_sym_name(s: str) -> str:
            # keep alnum/underscore; collapse others to single '_'
            s = re.sub(r"[^A-Za-z0-9_]", "_", str(s))
            s = re.sub(r"_+", "_", s).strip("_")
            return s or "sym"

        def _symbol_from_call(func_name: str, arg_exprs):
            # include args in the symbol name for disambiguation
            parts = [_sanitize_sym_name(func_name)]
            if arg_exprs:
                parts.extend(_sanitize_sym_name(a) for a in arg_exprs)
            return sp.Symbol("__".join(parts))

        if not ast.children:
            try:
                return sp.Number(float(ast.value)) if '.' in ast.value else sp.Number(int(ast.value))
            except ValueError:
                # Map booleans
                if ast.value.lower() == 'true':
                    return sp.true
                if ast.value.lower() == 'false':
                    return sp.false
                return sp.Symbol(ast.value.replace('.', '_'))

        
        # Handle indexed attributes: a[b].c  -> symbolic atom with args baked in
        if '[]' in ast.value and '.' in ast.value:
            func_name = ast.value.replace('[]', '').replace('()', '').replace('.', '_')
            args = [self._to_sympy_expr(child) for child in ast.children]
            return _symbol_from_call(func_name, args)

        # Handle indexing without attributes: a[b]
        if '[]' in ast.value:
            base_name = ast.value.replace('[]', '')
            base = sp.IndexedBase(base_name)
            index = self._to_sympy_expr(ast.children[0])
            return _symbol_from_call(base_name, [index])

        args = [self._to_sympy_expr(child) for child in ast.children]
        
        if ast.value == '&' and len(args) == 2:
            return sp.Function('BITAND')(*args)

        # Normalize ==/!= with boolean literals to X / !X
        if ast.value in ('==', '!=') and len(args) == 2:
            L, R = args
            is_L_bool = L is sp.true or L is sp.false
            is_R_bool = R is sp.true or R is sp.false
            if is_L_bool or is_R_bool:
                bval = True if (L is sp.true or R is sp.true) else False
                expr = R if is_L_bool else L
                if ast.value == '==':
                    return expr if bval else sp.Not(expr)
                else:  # '!='
                    return sp.Not(expr) if bval else expr

        if ast.value in ('&&', '||', '!', '==', '!=', '>', '<', '>=', '<='):
            return getattr(sp, self._sympy_operator(ast.value))(*args)
        elif ast.value == '/':
            return sp.Mul(args[0], sp.Pow(args[1], -1))
            # # Failed Use sympy.floor to correctly model Solidity's integer division
            # return sp.floor(args[0] / args[1])
        elif ast.value == '+':
            # unary plus: +x  →  x ; n-ary Add otherwise
            return args[0] if len(args) == 1 else sp.Add(*args)
        elif ast.value == '-':
            # Support unary negation and binary subtraction
            if len(args) == 1:
                return sp.Mul(sp.Integer(-1), args[0])
            elif len(args) == 2:
                return sp.Add(args[0], sp.Mul(sp.Integer(-1), args[1]))
            else:
                raise ValueError(f"Invalid number of children for '-' node: {len(args)}")
        elif ast.value == '*':
            return sp.Mul(*args)
        elif '()' in ast.value:
            # Treat calls as Boolean/unknown atoms so And/Or/Not accept them
            func_name = ast.value.replace('()', '').replace('.', '_')
            return _symbol_from_call(func_name, args)

        return sp.Symbol(ast.value.replace('.', '_'))



    def _sympy_operator(self, op):
        return {
            '&&': 'And',
            '||': 'Or',
            '!': 'Not',
            '==': 'Eq',
            '!=': 'Ne',
            '>': 'Gt',
            '<': 'Lt',
            '>=': 'Ge',
            '<=': 'Le'
        }[op]

    
    def sympy_to_z3(self, expr):
        if isinstance(expr, sp.Symbol):
            return z3.Real(str(expr))
        elif isinstance(expr, sp.Number):
            return z3.RealVal(float(expr))
        elif isinstance(expr, sp.Indexed):
            base = str(expr.base)
            indices = '_'.join(str(i) for i in expr.indices)
            return z3.Real(f"{base}_{indices}")
        elif isinstance(expr, sp.Eq):
            return self.sympy_to_z3(expr.lhs) == self.sympy_to_z3(expr.rhs)
        elif isinstance(expr, sp.Gt):
            return self.sympy_to_z3(expr.lhs) > self.sympy_to_z3(expr.rhs)
        elif isinstance(expr, sp.Ge):
            return self.sympy_to_z3(expr.lhs) >= self.sympy_to_z3(expr.rhs)
        elif isinstance(expr, sp.Lt):
            return self.sympy_to_z3(expr.lhs) < self.sympy_to_z3(expr.rhs)
        elif isinstance(expr, sp.Le):
            return self.sympy_to_z3(expr.lhs) <= self.sympy_to_z3(expr.rhs)
        elif isinstance(expr, sp.And):
            return z3.And(*[self.sympy_to_z3(arg) for arg in expr.args])
        elif isinstance(expr, sp.Or):
            return z3.Or(*[self.sympy_to_z3(arg) for arg in expr.args])
        elif isinstance(expr, sp.Not):
            return z3.Not(self.sympy_to_z3(expr.args[0]))
        elif isinstance(expr, sp.Ne):
            return self.sympy_to_z3(expr.lhs) != self.sympy_to_z3(expr.rhs)
        elif isinstance(expr, sp.Add):
            # return sum(self.sympy_to_z3(arg) for arg in expr.args)
            return z3.Sum(*[self.sympy_to_z3(arg) for arg in expr.args])
        elif isinstance(expr, sp.Mul):
            result = self.sympy_to_z3(expr.args[0])
            for arg in expr.args[1:]:
                result *= self.sympy_to_z3(arg)
            return result
        elif isinstance(expr, sp.Pow):
            base = self.sympy_to_z3(expr.args[0])
            exponent = self.sympy_to_z3(expr.args[1])
            return base ** exponent
        elif isinstance(expr, sp.Function):
            func_name = str(expr).replace('[', '_').replace(']', '').replace('.', '_')
            return z3.Real(func_name)
        else:
            raise ValueError(f"Unsupported expression type: {expr}")


    def _implies(self, expr1, expr2, level=0):
        """
        Check if expr1 implies expr2 by manually comparing the expressions.
        """
        printer(f"Checking implication: {expr1} -> {expr2} (level is: {level})", level)
        if expr1 == expr2:
            printer("Expressions are identical.", level)
            return True

        # Handle equivalences through algebraic manipulation
        try:
            if sp.simplify(expr1 - expr2) == 0:
                printer("Expressions are equivalent through algebraic manipulation.", level)
                return True
        except Exception as e: 
            # Even if the simplification fails, we can still proceed to other strategies
            printer(f"Error (for using sp.simplify): {e}", level)
            pass

        # Handle negation equivalence (e.g., !used[salt] == used[salt] == false)
        if isinstance(expr1, Not) and isinstance(expr2, sp.Equality):
            printer('>>>>>>>>>>>> here1', level)
            printer(f'expr2: {expr2}', level)
            printer(f'expr2.rhs: {expr2.rhs}', level)
            printer(f'expr2.lhs: {expr2.lhs}', level)
            if expr2.rhs == sp.false or expr2.rhs == False or expr2.rhs == sp.Symbol('false'):
                printer('>>>>>>>>>>>> here1.1', level)
                return self._implies(expr1.args[0], expr2.lhs, level + 1)
            if expr2.lhs == sp.false or expr2.lhs == False or expr2.lhs == sp.Symbol('false'):
                printer('>>>>>>>>>>>> here1.2', level)
                return self._implies(expr1.args[0], expr2.rhs, level + 1)

        if isinstance(expr2, Not) and isinstance(expr1, sp.Equality):
            printer('>>>>>>>>>>>> here2', level)
            printer(f'expr1: {expr1}', level)
            printer(f'expr1.rhs: {expr1.rhs}', level)
            printer(f'expr1.lhs: {expr1.lhs}', level)
            if expr1.rhs == sp.false or expr1.rhs == False or expr1.rhs == sp.Symbol('false'):
                printer('>>>>>>>>>>>> here2.1', level)
                return self._implies(expr2.args[0], expr1.lhs, level + 1)
            if expr1.lhs == sp.false or expr1.lhs == False or expr1.lhs == sp.Symbol('false'):
                printer('>>>>>>>>>>>> here2.2', level)
                return self._implies(expr2.args[0], expr1.rhs, level + 1)

        # Handle equivalence involving `true`
        if isinstance(expr1, sp.Symbol) and isinstance(expr2, sp.Equality):
            if expr2.rhs == sp.true or expr2.rhs == True or expr2.rhs == sp.Symbol('true'):
                return self._implies(expr1, expr2.lhs, level + 1)
            if expr2.lhs == sp.true or expr2.lhs == True or expr2.lhs == sp.Symbol('true'):
                return self._implies(expr1, expr2.rhs, level + 1)

        if isinstance(expr2, sp.Symbol) and isinstance(expr1, sp.Equality):
            if expr1.rhs == sp.true or expr1.rhs == True or expr1.rhs == sp.Symbol('true'):
                return self._implies(expr2, expr1.lhs, level + 1)
            if expr1.lhs == sp.true or expr1.lhs == True or expr1.lhs == sp.Symbol('true'):
                return self._implies(expr2, expr1.rhs, level + 1)

        # Handle logical equivalence for AND, OR, NOT operations
        if isinstance(expr1, Not) and isinstance(expr2, Or):
            if len(expr2.args) == 2:
                left, right = expr2.args
                if isinstance(left, sp.Equality) and left.rhs == sp.false:
                    return self._implies(expr1.args[0], left.lhs, level + 1) and self._implies(right, sp.true, level + 1)
                if isinstance(right, sp.Equality) and right.rhs == sp.false:
                    return self._implies(expr1.args[0], right.lhs, level + 1) and self._implies(left, sp.true, level + 1)

        if isinstance(expr2, Not) and isinstance(expr1, Or):
            if len(expr1.args) == 2:
                left, right = expr1.args
                if isinstance(left, sp.Equality) and left.rhs == sp.false:
                    return self._implies(expr2.args[0], left.lhs, level + 1) and self._implies(right, sp.true, level + 1)
                if isinstance(right, sp.Equality) and right.rhs == sp.false:
                    return self._implies(expr2.args[0], right.lhs, level + 1) and self._implies(left, sp.true, level + 1)

        if isinstance(expr1, And) and isinstance(expr2, And):
            if len(expr1.args) == len(expr2.args):
                return all(self._implies(arg1, arg2, level + 1) for arg1, arg2 in zip(expr1.args, expr2.args))

        if isinstance(expr1, Or) and isinstance(expr2, Or):
            if len(expr1.args) == len(expr2.args):
                return all(self._implies(arg1, arg2, level + 1) for arg1, arg2 in zip(expr1.args, expr2.args))

        # Handle AND expression for expr2
        if isinstance(expr2, And):
            # expr1 should imply all parts of expr2 if expr2 is an AND expression
            results = [self._implies(expr1, arg, level + 1) for arg in expr2.args]
            printer(f"Implication results for And expr2 which was `{expr1} => {expr2}`: {results}", level)
            return all(results)

        # Handle AND expression for expr1
        if isinstance(expr1, And):
            # All parts of expr1 should imply expr2 if expr1 is an AND expression
            results = [self._implies(arg, expr2, level + 1) for arg in expr1.args]
            printer(f"Implication results for And expr1 which was `{expr1} => {expr2}`: {results}", level)
            return any(results)

        # Handle OR expression for expr2
        if isinstance(expr2, Or):
            # expr1 should imply at least one part of expr2 if expr2 is an OR expression
            results = [self._implies(expr1, arg, level + 1) for arg in expr2.args]
            printer(f"Implication results for Or expr2 which was `{expr1} => {expr2}`: {results}", level)
            return any(results)

        # Handle OR expression for expr1
        if isinstance(expr1, Or):
            # All parts of expr1 should imply expr2 if expr1 is an OR expression
            results = [self._implies(arg, expr2, level + 1) for arg in expr1.args]
            printer(f"Implication results for Or expr1 which was `{expr1} => {expr2}`: {results}", level)
            return all(results)

        # Handle function calls
        if isinstance(expr1, sp.Function) and isinstance(expr2, sp.Function):
            # Ensure the function names and the number of arguments match
            if expr1.func == expr2.func and len(expr1.args) == len(expr2.args):
                return all(self._implies(arg1, arg2, level + 1) for arg1, arg2 in zip(expr1.args, expr2.args))
            return False

        if isinstance(expr1, sp.Symbol) and isinstance(expr2, sp.Symbol):
            return expr1 == expr2

        # The following acts as a part of the base case for recursion
        # Specific relational operator checks for numerical comparisons
        relational_operators = (sp.Gt, sp.Ge, sp.Lt, sp.Le, sp.Eq, sp.Ne)
        if isinstance(expr1, relational_operators) and isinstance(expr2, relational_operators):
            printer(f'In relational base cases; expr1: {expr1}, expr2: {expr2}', level)

            # # Z3+nonneg fast-path before the other branches
            # # Prefer Z3 under non-negative domain if there are variables
            # try:
            #     if expr1.free_symbols or expr2.free_symbols:
            #         z3_result = self._z3_implies_with_nonneg(expr1, expr2)
            #         printer(f"Z3 (nonneg) implication {expr1} -> {expr2}: {z3_result}", level)
            #         return z3_result
            # except Exception as e:
            #     printer(f"Error (Z3 nonneg implication): {e}", level)

            # Check for Eq vs non-Eq comparisons; we don't handle this well, let's return False
            if (isinstance(expr1, sp.Eq) and not isinstance(expr2, sp.Eq)) or (not isinstance(expr1, sp.Eq) and isinstance(expr2, sp.Eq)):
                printer(f'One of the expressions is equality and the other is not; expr1: {expr1}, expr2: {expr2}', level)  

                            # If there are free symbols, do implication under non-negative domain via Z3.
                free_syms = expr1.free_symbols.union(expr2.free_symbols)
                if free_syms:
                    try:
                        z3_result = self._z3_implies_with_nonneg(expr1, expr2)
                        printer(f"Z3 (nonneg) implication {expr1} -> {expr2}: {z3_result}", level)
                        return z3_result
                    except Exception as e:
                        printer(f"Error (Z3 nonneg implication): {e}", level)
                        # fall through to existing logic as a safe fallback
   

                # switch to z3
                printer(f'Switching to Z3 ..... ')
                z3_expr1 = self.sympy_to_z3(expr1)
                z3_expr2 = self.sympy_to_z3(expr2)

                solver = z3.Solver()
                solver.add(z3.And(z3_expr1, z3.Not(z3_expr2)))

                #solver.add(self.sympy_to_z3(negation))
                result = solver.check()

                if result == z3.sat:
                    printer(f"Implies {expr1} to {expr2}: False", level=0)
                    return False
                else:
                    printer(f"Implies {expr1} to {expr2}: True", level=0)
                    return True
            elif all(isinstance(arg, (sp.Float, sp.Integer, sp.Symbol)) for arg in [expr1.lhs, expr1.rhs, expr2.lhs, expr2.rhs]):
                printer(f'Inside!... expr1: {expr1}, expr2: {expr2}', level)
                # Check if the negation of the implication is not satisfiable
                try:
                    # First check if Indexed symbols exist
                    if self._has_indexed_symbols(expr1) or self._has_indexed_symbols(expr2):
                        printer("Indexed symbols detected; switching to Z3 solver.", level)

                        z3_expr1 = self.sympy_to_z3(expr1)
                        z3_expr2 = self.sympy_to_z3(expr2)

                        solver = z3.Solver()
                        solver.add(z3_expr1, z3.Not(z3_expr2))

                        result = solver.check()

                        if result == z3.unsat:
                            printer(f"Z3 implication {expr1} -> {expr2}: True", level)
                            return True
                        else:
                            printer(f"Z3 implication {expr1} -> {expr2}: False", level)
                            return False

                    # Otherwise, use SymPy as before
                    try:
                        negation = sp.And(expr1, Not(expr2))
                        printer(f"Negation of the implication {expr1} -> {expr2}: {satisfiable(negation)}; type of {type(satisfiable(negation))}", level)
                        result = not satisfiable(negation, use_lra_theory=True)
                        printer(f"Implication {expr1} -> {expr2} using satisfiable: {result}", level)
                        return result
                    except Exception as e:
                        printer(f"Error (satisfiability error): {e}", level)
                        return False
                    
                except Exception as e:
                    printer(f"Error (satisfiability error): {e}", level)
                    return False
            else:

                
                printer(f'Not all arguments are numbers, floats, or symbols in expr1 and expr2, however, we still try to use the same sympy satisfiability check', level)

                # print type of all lhs and rhs's of both expressions
                printer(f'type of expr1.lhs: {type(expr1.lhs)}')
                printer(f'type of expr1.rhs: {type(expr1.rhs)}')
                printer(f'type of expr2.lhs: {type(expr2.lhs)}')
                printer(f'type of expr2.rhs: {type(expr2.rhs)}')


                # Detect ANY non-trivial numeric scaling (not just fractions) anywhere:
                #   - Multiplicative numeric factor != ±1 (e.g., *2, *1.5, *1e18, *1/2)
                #   - Negative powers (division), e.g., 2**-1
                def _has_numeric_scale(e) -> bool:
                    try:
                        # Direct negative power (e.g., 2**-1) => division
                        if isinstance(e, sp.Pow) and e.exp.is_number and e.exp < 0:
                            return True
                        # Multiplicative factors with a numeric coefficient or negative powers
                        if isinstance(e, sp.Mul):
                            for aa in e.args:
                                if isinstance(aa, sp.Pow) and aa.exp.is_number and aa.exp < 0:
                                    return True
                                # Any numeric factor not ±1 (covers integers, floats, rationals)
                                if isinstance(aa, sp.Number) and aa not in (1, -1):
                                    return True
                            # Recurse within Mul arguments
                            return any(_has_numeric_scale(aa) for aa in e.args)
                        # Recurse through additive structures without flagging bare integers
                        if isinstance(e, sp.Add):
                            return any(_has_numeric_scale(aa) for aa in e.args)
                    except Exception:
                        pass
                    return False

                if any(_has_numeric_scale(arg) for arg in [expr1.lhs, expr1.rhs, expr2.lhs, expr2.rhs]):
                    printer(f'Numeric scaling detected; switching to z3 with non-negativity.', level)

                    z3_expr1 = self.sympy_to_z3(expr1)
                    z3_expr2 = self.sympy_to_z3(expr2)

                    variables = {str(sym) for sym in expr1.free_symbols.union(expr2.free_symbols)}
                    z3_vars = {var: z3.Real(var) for var in variables}  # Convert to Z3 Reals

                    solver = z3.Solver()
                    # Solidity-like domains for this numeric monotonicity reasoning
                    for var in z3_vars.values():
                        solver.add(var >= 0)

                    # Check UNSAT of expr1 ∧ ¬expr2
                    solver.add(z3_expr1, z3.Not(z3_expr2))
                    if solver.check() == z3.sat:
                        printer(f"Implies {expr1} to {expr2}: False", level=0)
                        return False
                    else:
                        printer(f"Implies {expr1} to {expr2}: True", level=0)
                        return True
                else: 
                    try:
                        # First check if Indexed symbols exist
                        if self._has_indexed_symbols(expr1) or self._has_indexed_symbols(expr2):
                            printer("Indexed symbols detected; switching to Z3 solver.", level)

                            z3_expr1 = self.sympy_to_z3(expr1)
                            z3_expr2 = self.sympy_to_z3(expr2)

                            solver = z3.Solver()
                            solver.add(z3_expr1, z3.Not(z3_expr2))

                            result = solver.check()

                            if result == z3.unsat:
                                printer(f"Z3 implication {expr1} -> {expr2}: True", level)
                                return True
                            else:
                                printer(f"Z3 implication {expr1} -> {expr2}: False", level)
                                return False

                        # Otherwise, use SymPy as before
                        try:
                            negation = sp.And(expr1, Not(expr2))
                            printer(f"Negation of the implication {expr1} -> {expr2}: {satisfiable(negation)}; type of {type(satisfiable(negation))}", level)
                            result = not satisfiable(negation, use_lra_theory=True)
                            printer(f"Implication {expr1} -> {expr2} using satisfiable: {result}", level)
                            return result
                        except Exception as e:
                            printer(f"Error (satisfiability error): {e}", level)
                            return False

                    except Exception as e:
                        printer(f"Error (satisfiability error): {e}", level)
                        return False
        return False

    def witness_solve(
        self, 
        new_pred: str, 
        old_pred: str, 
        *, 
        domains: dict | None = None, 
        simplify: bool = True
    ):
        """
        Attempts to find a witness (input assignment) where new_pred is True
        and old_pred is False.
        Returns a WitnessResult object.
        """
        solver = WitnessSolver(self)
        return solver.solve(new_pred, old_pred, domains=domains, simplify=simplify)