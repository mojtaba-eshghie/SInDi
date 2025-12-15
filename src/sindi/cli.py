# src/sindi/cli.py
#!/usr/bin/env python3
import argparse
import io
import json
import sys
from typing import Any, Dict
from contextlib import redirect_stdout
from .rewriter import Rewriter
from .tokenizer import Tokenizer
from .parser import Parser, ASTNode
from .simplifier import Simplifier
from .comparator import Comparator
from .witness import DomainSpec
from .utils import printer, set_quiet, set_debug
from .comparator_light import ComparatorRulesOnly
import os

def _env_truthy(name: str) -> bool:
    return os.environ.get(name, "").strip().lower() in ("1", "true", "yes", "on")

def _configure_logging(args) -> None:
    if getattr(args, "debug_logs", False):
        set_debug(True)
    elif _env_truthy("SINDI_DEBUG"):
        set_debug(True)
    else:
        set_quiet(True)
    if _env_truthy("SINDI_QUIET"):
        set_quiet(True)

def ast_to_dict(n: ASTNode) -> Dict[str, Any]:
    return {"value": n.value, "children": [ast_to_dict(c) for c in n.children]}

def print_tree(n: ASTNode, indent: int = 0) -> None:
    pad = "  " * indent
    print(f"{pad}{n.value}")
    for c in n.children:
        print_tree(c, indent + 1)

def read_predicate(value: str, is_file: bool) -> str:
    if not is_file:
        return value
    with open(value, "r", encoding="utf-8") as f:
        return f.read().strip()

# --- Existing Commands (Rewrite, Tokenize, Parse, Simplify) ---

def cmd_rewrite(args: argparse.Namespace) -> int:
    _configure_logging(args)
    rw = Rewriter()
    s = read_predicate(args.predicate, args.from_file)
    print(rw.apply(s))
    return 0

def cmd_tokenize(args: argparse.Namespace) -> int:
    _configure_logging(args)
    rw = Rewriter()
    tk = Tokenizer()
    s = read_predicate(args.predicate, args.from_file)
    if not args.skip_rewrite:
        s = rw.apply(s)
    tokens = tk.tokenize(s)
    if args.json:
        print(json.dumps([{"value": v, "tag": t} for (v, t) in tokens], ensure_ascii=False))
    else:
        print(tokens)
    return 0

def cmd_parse(args: argparse.Namespace) -> int:
    _configure_logging(args)
    rw = Rewriter()
    tk = Tokenizer()
    s = read_predicate(args.predicate, args.from_file)
    if not args.skip_rewrite:
        s = rw.apply(s)
    tokens = tk.tokenize(s)
    ast = Parser(tokens).parse()
    if args.tree:
        print_tree(ast)
    elif args.json:
        print(json.dumps(ast_to_dict(ast), ensure_ascii=False))
    else:
        print(ast)
    return 0

def cmd_simplify(args: argparse.Namespace) -> int:
    _configure_logging(args)
    rw = Rewriter()
    tk = Tokenizer()
    sp = Simplifier()
    s = read_predicate(args.predicate, args.from_file)
    if not args.skip_rewrite:
        s = rw.apply(s)
    tokens = tk.tokenize(s)
    ast = Parser(tokens).parse()
    simplified = sp.simplify(ast)
    out: Dict[str, Any] = {"simplified_ast": ast_to_dict(simplified)}
    if args.show_sympy:
        try:
            out["sympy_expr_original"] = str(sp._to_sympy(ast))          # type: ignore[attr-defined]
        except Exception as e:
            out["sympy_expr_original_error"] = str(e)
        try:
            out["sympy_expr_simplified"] = str(sp._to_sympy(simplified)) # type: ignore[attr-defined]
        except Exception as e:
            out["sympy_expr_simplified_error"] = str(e)
    if args.json:
        print(json.dumps(out, ensure_ascii=False))
    else:
        if args.show_sympy:
            if "sympy_expr_original" in out:
                print("SymPy (original):", out["sympy_expr_original"])
            if "sympy_expr_simplified" in out:
                print("SymPy (simplified):", out["sympy_expr_simplified"])
        print("Simplified AST:")
        print_tree(simplified)
    return 0

def cmd_compare(args: argparse.Namespace) -> int:
    _configure_logging(args)
    rw = Rewriter()
    tk = Tokenizer()
    p1 = read_predicate(args.predicate1, args.p1_file)
    p2 = read_predicate(args.predicate2, args.p2_file)
    if args.light:
        cmp = ComparatorRulesOnly(verbose=args.verbose)
    else:
        cmp = Comparator()
    sink = io.StringIO()
    with redirect_stdout(sink):
        verdict = cmp.compare(p1, p2)
    if not args.verbose and not args.json:
        print(verdict)
        return 0
    out: Dict[str, Any] = {"verdict": verdict}
    rp1 = rw.apply(p1)
    rp2 = rw.apply(p2)
    out["rewritten"] = {"p1": rp1, "p2": rp2}
    ast1 = Parser(tk.tokenize(rp1)).parse()
    ast2 = Parser(tk.tokenize(rp2)).parse()
    out["ast"] = {"p1": ast_to_dict(ast1), "p2": ast_to_dict(ast2)}
    if args.json:
        print(json.dumps(out, ensure_ascii=False))
    else:
        print("Verdict:", verdict)
        print("\n[Rewritten]\n p1:", rp1, "\n p2:", rp2)
        print("\n[AST p1]")
        print_tree(ast1)
        print("\n[AST p2]")
        print_tree(ast2)
    return 0

# --- NEW: Witness Command ---

def parse_domains(domain_str: str) -> Dict[str, DomainSpec]:
    """Parses 'val:uint8,flag:bool' into domain dict."""
    if not domain_str:
        return {}
    domains = {}
    for part in domain_str.split(','):
        if ':' not in part:
            continue
        var, spec = part.split(':', 1)
        var = var.strip()
        spec = spec.strip().lower()
        
        if spec == 'bool':
            domains[var] = DomainSpec(kind='bool')
        elif spec.startswith('uint'):
            # handle uint, uint8, uint256
            bits = 256
            if len(spec) > 4:
                try: bits = int(spec[4:])
                except: pass
            domains[var] = DomainSpec(kind='uint', bits=bits)
        elif spec.startswith('int'):
            bits = 256
            if len(spec) > 3:
                try: bits = int(spec[3:])
                except: pass
            domains[var] = DomainSpec(kind='int', bits=bits)
        elif spec == 'address':
            domains[var] = DomainSpec(kind='address')
    return domains

def cmd_witness(args: argparse.Namespace) -> int:
    _configure_logging(args)
    
    # Read Predicates
    new_pred = read_predicate(args.new_pred, args.new_file)
    old_pred = read_predicate(args.old_pred, args.old_file)
    
    # Parse Domains
    domains = parse_domains(args.domains) if args.domains else None
    
    # Solve
    comp = Comparator()
    res = comp.witness_solve(new_pred, old_pred, domains=domains)
    
    # Output
    out = {
        "sat": res.sat,
        "model": res.model,
        "error": res.error,
        "unconstrained": res.unconstrained
    }
    
    if args.verbose:
        out["z3_formula"] = res.z3_formula
        out["simplified_new"] = res.simplified_new
        out["simplified_old"] = res.simplified_old
        
    if args.json:
        print(json.dumps(out, indent=2, ensure_ascii=False))
    else:
        if res.sat is True:
            print("Status: SAT (Weakening Found)")
            print("Witness Model:")
            for k, v in res.model.items():
                print(f"  {k} = {v}")
        elif res.sat is False:
            print("Status: UNSAT (No weakening found / Equivalent)")
        else:
            print(f"Status: ERROR/UNKNOWN ({res.error})")
            
    return 0 if res.sat is not None else 1

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="sindi",
        description="SInDi CLI: rewrite, tokenize, parse, simplify, compare, and generate witnesses for Solidity predicates."
    )
    sub = p.add_subparsers(dest="cmd", required=True)
    
    # Rewrite
    pr = sub.add_parser("rewrite", help="Apply rewrite rules and print the result.")
    pr.add_argument("predicate")
    pr.add_argument("--from-file", action="store_true")
    pr.set_defaults(func=cmd_rewrite)
    
    # Tokenize
    pt = sub.add_parser("tokenize", help="Tokenize (optionally after rewrite).")
    pt.add_argument("predicate")
    pt.add_argument("--from-file", action="store_true")
    pt.add_argument("--skip-rewrite", action="store_true")
    pt.add_argument("--json", action="store_true")
    pt.set_defaults(func=cmd_tokenize)
    
    # Parse
    pp = sub.add_parser("parse", help="Parse into AST (optionally after rewrite).")
    pp.add_argument("predicate")
    pp.add_argument("--from-file", action="store_true")
    pp.add_argument("--skip-rewrite", action="store_true")
    pp.add_argument("--tree", action="store_true")
    pp.add_argument("--json", action="store_true")
    pp.set_defaults(func=cmd_parse)
    
    # Simplify
    ps = sub.add_parser("simplify", help="Simplify AST (SymPy-backed).")
    ps.add_argument("predicate")
    ps.add_argument("--from-file", action="store_true")
    ps.add_argument("--skip-rewrite", action="store_true")
    ps.add_argument("--show-sympy", action="store_true")
    ps.add_argument("--json", action="store_true")
    ps.set_defaults(func=cmd_simplify)
    
    # Compare
    pc = sub.add_parser("compare", help="Compare two predicates and print verdict.")
    pc.add_argument("predicate1")
    pc.add_argument("predicate2")
    pc.add_argument("--p1-file", action="store_true")
    pc.add_argument("--p2-file", action="store_true")
    pc.add_argument("--light", action="store_true", help="Use solver-free ComparatorRulesOnly.")
    pc.add_argument("--verbose", action="store_true", help="Show rewritten predicates and ASTs.")
    pc.add_argument("--json", action="store_true")
    pc.add_argument("--debug-logs", action="store_true", help="Do not silence internal debug prints.")
    pc.set_defaults(func=cmd_compare)

    # Witness (NEW)
    pw = sub.add_parser("witness", help="Find a variable assignment satisfying New AND NOT Old.")
    pw.add_argument("new_pred", help="The new (weaker?) predicate")
    pw.add_argument("old_pred", help="The old (stronger?) predicate")
    pw.add_argument("--new-file", action="store_true", help="Read new_pred from file")
    pw.add_argument("--old-file", action="store_true", help="Read old_pred from file")
    pw.add_argument("--domains", help="Comma-separated domains, e.g. 'x:uint8,flag:bool'")
    pw.add_argument("--json", action="store_true", help="Output JSON result")
    pw.add_argument("--verbose", action="store_true", help="Include debug formulas in JSON")
    pw.set_defaults(func=cmd_witness)

    return p

def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    try:
        return args.func(args)
    except KeyboardInterrupt:
        print("Interrupted.", file=sys.stderr)
        return 130
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1

if __name__ == "__main__":
    sys.exit(main())