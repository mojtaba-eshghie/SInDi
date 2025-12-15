# Δ Sindi: Semantic Invariant Differencing for Solidity Smart Contracts

Sindi compares two Solidity boolean predicates (e.g., the guards in `require`/`assert`) and decides whether they are **equivalent**, **one is stronger**, or **unrelated**. It’s designed to survive real-world Solidity syntax variations across versions and frameworks (e.g., OpenZeppelin patterns) by normalizing source, tokenizing, parsing to an AST, and reasoning over the structure.

Sindi also includes a **Witness Generator**. If a predicate is weakened (e.g., a security check is relaxed), Sindi can produce a concrete variable assignment that passes the new check but fails the old one—a counter-example proving the regression.

---

## Why Sindi?

* **Contract evolution:** When you refactor or upgrade a contract (proxy patterns, library changes, Solidity version bumps), the *same* invariant often appears in a different syntactic form. Sindi checks whether behavior is preserved.
* **Security Regression Testing:** Automatically detect if a code change accidentally loosens a constraint (e.g., `x < 100` becoming `x <= 100`). Sindi provides the exact input (`x=100`) that triggers the regression.
* **Invariant denoising:** Auto-mined invariants can be redundant or weak. Sindi helps find equivalences and strength relationships to keep only the strongest set.

---

## What it does

* **Rewrite & Normalize (cross-version)**
  Canonicalizes common Solidity constructs before parsing. Examples:
  * `now` → `block.timestamp`
  * `_msgSender()` → `msg.sender`
  * `isOwner()` → `msg.sender == owner()`
  * Zero address hex → `address(0)`
  * `SafeMath.add(x,y)` / `a.add(b)` → `(x) + (y)`
  * `type(IERC721).interfaceId` ↔ the equivalent hex ID

* **Tokenize → Parse (AST)**
  Converts the normalized predicate into an AST that captures expressions, calls, indexing, logical/relational ops, etc.

* **Simplify (symbolic)**
  Converts to SymPy expressions and simplifies (with careful mappings for Solidity-like expressions).

* **Compare (semantic differencing)**
  Checks implication relationships and returns one of:
  * `The predicates are equivalent.`
  * `The first predicate is stronger.` (Regression / Relaxed constraint)
  * `The second predicate is stronger.` (Strengthened constraint)
  * `The predicates are not equivalent and neither is stronger.`

* **Witness Generation (Counter-examples)**
  Solves for inputs that satisfy `New_Predicate AND NOT Old_Predicate`.
  * Handles **strict typing** (Booleans vs Numbers).
  * Supports **Solidity domains** (`uint`, `int`, `address` bounds).
  * Returns concrete models (e.g., `{'x': 100, 'paused': False}`).

---

## Installation

### From PyPI

```bash
pip install Sindi
```

### From source (this repo)

```bash
# Clone, then in repo root:
python -m pip install -r requirements.txt
# Optional: editable install
python -m pip install -e .

```

**Requirements:** Python 3.8+
The comparator uses `z3-solver` (already listed in requirements).

---

## Quick start (CLI)The CLI is exposed via `main.py` (or `sindi` if installed):

```bash
Sindi rewrite   <predicate> [--from-file]
Sindi tokenize  <predicate> [--json]
Sindi parse     <predicate> [--tree|--json]
Sindi simplify  <predicate> [--show-sympy]
Sindi compare   <p1> <p2> [--light] [--verbose|--json]
Sindi witness   <new_pred> <old_pred> [--domains "var:type"] [--json]
```

### 1. Comparison

```bash
python main.py compare "msg.sender == msg.origin && a >= b" "msg.sender == msg.origin"
# -> The first predicate is stronger.
```

### 2. Witness Generation (Find Security Regression)

If you suspect a constraint was weakened, ask for a witness:

```bash
# Example: Boundary weakening
python main.py witness "x <= 100" "x < 100"
# Output:
# Status: SAT (Weakening Found)
# Witness Model:
#   x = 100
```

**With specific domains:**
Sometimes `x != 0` and `x > 0` look different unless you know `x` is a `uint`.

```bash
python main.py witness "val != 0" "val > 0" --domains "val:uint"
# Output:
# Status: UNSAT (No weakening found / Equivalent)
```

**Complex Boolean Logic:**

```bash
python main.py witness "paused || shutdown" "paused" --domains "shutdown:bool"
# Output:
# Status: SAT (Weakening Found)
# Witness Model:
#   shutdown = True
#   paused = False

```

---

##Python APIIf you installed from PyPI:

```python
from src.sindi.comparator import Comparator
from src.sindi.witness import DomainSpec

cmp = Comparator()

# 1. Compare
print(cmp.compare("a < b", "a <= b"))
# "The first predicate is stronger."

# 2. Generate Witness
res = cmp.witness_solve(
    new_pred="val <= 100", 
    old_pred="val < 100",
    domains={"val": DomainSpec(kind="uint")}
)

if res.sat:
    print(f"Regression found! Input: {res.model}")
    # Regression found! Input: {'val': 100}

```

You can also use building blocks:

```python
from src.sindi.rewriter import Rewriter
from src.sindi.tokenizer import Tokenizer
from src.sindi.parser import Parser

rw, tk = Rewriter(), Tokenizer()
s = rw.apply("SafeMath.add(a,b) > c")
ast = Parser(tk.tokenize(s)).parse()
```

---

## The pipeline (architecture at a glance)

1. **Rewriting / Normalization** (string → string)
Fixes cross-version and library-specific surface differences.
2. **Tokenization & Parsing** (string → tokens → AST)
Produces a structured AST (`ASTNode`).
3. **Simplification** (AST → SymPy → simplified AST)
Uses symbolic math to normalize expressions.
4. **Comparison** (AST/SymPy → verdict)
Symbolic checks + selective SMT (Z3) to prove implication.
5. **Witness Solver** (SymPy → Typed Z3)
Infers types (`Bool` vs `Real`), applies domain constraints (`uint256`), and solves for counter-examples.

---

## Notes & limitations

* **Numerics / domains:** For comparison, variables are assumed non-negative by default (Solidity-like). Witness generation allows strict `uint`/`int` bit-width constraints.
* **Division:** We model `a / b` as `a * (b ** -1)` in symbolic form.
* **Functions & arrays:** Uninterpreted unless specialized; treated as symbols (e.g., `balanceOf(user)` is a symbol `balanceOf_user`).
* **Scope:** Focused on boolean predicates used in `require`/`assert`—not full contract semantics.

---

## Contributing

Issues and PRs are welcome. If you add rewrite rules or parser coverage, please include targeted tests.

---

## Citation (paper & code)

If you use Sindi in academic work, please cite the **Sindi** paper (upcoming) and this repository.

```bibtex
@techreport{SInDi,
  author      = {Eshghie, Mojtaba and Andersson Kasche, Gustav and Artho, Cyrille and Monperrus, Martin},
  title       = {{SInDi: Semantic Invariant Differencing for Solidity Smart Contracts}},
  institution = {KTH Royal Institute of Technology, Theoretical Computer Science Division},
  year        = {2025},
  type        = {Technical Report},
  url         = {[https://kth.diva-portal.org/smash/record.jsf?pid=diva2:1956137](https://kth.diva-portal.org/smash/record.jsf?pid=diva2:1956137)},
  note        = {Published via KTH DiVA Portal}
}

```

* Tool: `https://github.com/mojtaba-eshghie/Sindi`
* PyPI: `https://pypi.org/project/Sindi/`
