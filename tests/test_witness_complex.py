import unittest
import sys
import os

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))

from sindi.comparator import Comparator
from sindi.witness import DomainSpec

class TestWitnessComplex(unittest.TestCase):
    def setUp(self):
        self.comp = Comparator()

    def test_safemath_equivalence_uint(self):
        """
        Case: SafeMath (#4, #39, etc.)
        Old: require(b > 0)
        New: require(b != 0)
        
        Sindi defaults to assuming variables are non-negative (uint) unless specified.
        Therefore, by default, these SHOULD be equivalent.
        
        To prove the solver isn't just ignoring negatives, we first force a SIGNED int domain.
        """
        print("\n--- Running test_safemath_equivalence_uint ---")
        
        # 1. Force SIGNED int domain. 
        # Here, (b != 0) allows -1, but (b > 0) does not. 
        # We expect a witness (e.g., b = -1).
        res_signed = self.comp.witness_solve(
            "b != 0", 
            "b > 0",
            domains={"b": DomainSpec(kind="int")} # Explicitly allow negatives
        )
        print(f"[Signed Int Check] SAT: {res_signed.sat}, Model: {res_signed.model}")
        self.assertTrue(res_signed.sat, "With signed int domain, b=-1 should be a witness")
        
        # 2. Use Default (Implicit Uint) or Explicit Uint
        # Here, Sindi assumes b >= 0.
        # (b != 0 AND b >= 0) <==> (b > 0).
        # We expect UNSAT (Equivalent).
        res_uint = self.comp.witness_solve(
            "b != 0", 
            "b > 0",
            domains={"b": DomainSpec(kind="uint")} # Or just None, as default is >= 0
        )
        print(f"[UInt/Default Check] SAT: {res_uint.sat}")
        self.assertFalse(res_uint.sat, "With uint domain (default), b > 0 and b != 0 are equivalent")

    def test_uniswap_arithmetic_weakening(self):
        """
        Case: UniswapLibrary (#15)
        Old: amountOut > amountIn.sub(amountIn.div(slippage * 2))
        New: amountOut > amountIn.sub(amountIn.div(slippage / 2))
        
        Logic:
        Old subtraction: X / (2S)  (Subtracting a small amount -> Threshold is HIGH)
        New subtraction: X / (S/2) = 2X/S (Subtracting a large amount -> Threshold is LOW)
        
        Since the New threshold is LOWER, the condition is WEAKER.
        Witness: An amountOut that is valid in New (low threshold) but fails Old (high threshold).
        """
        print("\n--- Running test_uniswap_arithmetic_weakening ---")
        
        # Simplified representation of the diff
        # We use standard operators because Sindi rewrites .sub/.div anyway
        old_pred = "out > amountIn - (amountIn / (slip * 2))"
        new_pred = "out > amountIn - (amountIn / (slip / 2))"
        
        # Assume valid inputs to avoid division by zero issues in solver
        # slip=10, amountIn=100
        # Old sub: 100 / 20 = 5  -> out > 95
        # New sub: 100 / 5 = 20  -> out > 80
        # Expected witness: out = 90 (Satisfies >80, Fails >95)
        
        # We inject values directly to test the arithmetic logic
        old_p = old_pred.replace("slip", "10").replace("amountIn", "100")
        new_p = new_pred.replace("slip", "10").replace("amountIn", "100")
        
        res = self.comp.witness_solve(new_p, old_p)
        
        print(f"SAT: {res.sat}")
        print(f"Model: {res.model}")
        
        self.assertTrue(res.sat)
        out_val = res.model['out']
        # Check logic: 80 < out <= 95
        self.assertGreater(out_val, 80)
        self.assertLessEqual(out_val, 95)

    def test_logic_removal_atsui(self):
        """
        Case: AtsuiNft (#27)
        Old: require(price != 0 && phase >= p)
        New: require(phase >= p && prices[p] != price)
        
        The explicit 'price != 0' check was removed.
        Witness: price = 0 (assuming other conditions hold)
        """
        print("\n--- Running test_logic_removal_atsui ---")
        
        # We simulate the array access as a function or variable for the solver
        old_pred = "price != 0 && phase >= p"
        new_pred = "phase >= p && prices_p != price"
        
        res = self.comp.witness_solve(new_pred, old_pred)
        
        print(f"SAT: {res.sat}")
        print(f"Model: {res.model}")
        
        self.assertTrue(res.sat)
        self.assertEqual(res.model.get('price'), 0)
        self.assertNotEqual(res.model.get('prices_p'), 0)

    def test_lucks_executor_arithmetic_or(self):
        """
        Case: LucksExecutor (#38)
        Old: id == item_id
        New: id == item_id || (id + 100) == item_id
        
        Witness: id + 100 == item_id
        """
        print("\n--- Running test_lucks_executor_arithmetic_or ---")
        
        res = self.comp.witness_solve(
            "id == item_id || (id + 100) == item_id",
            "id == item_id"
        )
        
        print(f"SAT: {res.sat}")
        print(f"Model: {res.model}")
        
        self.assertTrue(res.sat)
        id_val = res.model['id']
        item_id_val = res.model['item_id']
        
        # Verify the witness follows the new logic branch
        self.assertEqual(id_val + 100, item_id_val)

if __name__ == '__main__':
    unittest.main()