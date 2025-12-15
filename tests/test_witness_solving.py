import unittest
import sys
import os

# Ensure src is in the path so we can import sindi
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))

from sindi.comparator import Comparator
from sindi.witness import DomainSpec

class TestWitnessSolving(unittest.TestCase):
    def setUp(self):
        self.comp = Comparator()

    def test_weakening_boundary(self):
        """
        Test detection of a relaxed boundary.
        Old: x < 100
        New: x <= 100
        Expected Witness: x = 100
        """
        print("\n--- Running test_weakening_boundary ---")
        res = self.comp.witness_solve("x <= 100", "x < 100")
        
        print(f"SAT: {res.sat}")
        print(f"Model: {res.model}")
        
        self.assertTrue(res.sat, "Should find a witness")
        self.assertEqual(res.model['x'], 100, "Witness for (x<=100 and !(x<100)) must be 100")

    def test_boolean_escape_hatch(self):
        """
        Test detection of a new OR condition (escape hatch).
        Old: paused
        New: paused || shutdown
        Expected Witness: paused=False, shutdown=True
        """
        print("\n--- Running test_boolean_escape_hatch ---")
        # Explicitly define domains to ensure 'paused' is treated as bool if not inferred
        res = self.comp.witness_solve(
            "paused || shutdown", 
            "paused",
            domains={
                "shutdown": DomainSpec(kind="bool"), 
                "paused": DomainSpec(kind="bool")
            }
        )
        
        print(f"SAT: {res.sat}")
        print(f"Model: {res.model}")
        
        self.assertTrue(res.sat)
        # Logic: (paused || shutdown) IS TRUE  AND  (paused) IS FALSE
        # Therefore: paused must be False, shutdown must be True.
        self.assertFalse(res.model.get('paused'), "Old predicate 'paused' must be false in witness")
        self.assertTrue(res.model.get('shutdown'), "New predicate 'shutdown' must be true in witness")

    def test_equivalence_unsat(self):
        """
        Test that semantically equivalent predicates produce no witness (UNSAT).
        Old: a + b > 10
        New: b + a > 10
        Expected: SAT=False
        """
        print("\n--- Running test_equivalence_unsat ---")
        res = self.comp.witness_solve("b + a > 10", "a + b > 10")
        
        print(f"SAT: {res.sat}")
        self.assertFalse(res.sat, "Equivalent predicates should not have a witness")

    def test_type_inference_mixed(self):
        """
        Test automatic type inference (Bool vs Real).
        New: x > 5 || emergency
        Old: x > 5
        'emergency' is used in a boolean context (||), 'x' in a numeric context (>).
        """
        print("\n--- Running test_type_inference_mixed ---")
        res = self.comp.witness_solve("x > 5 || emergency", "x > 5")
        
        print(f"SAT: {res.sat}")
        print(f"Model: {res.model}")
        
        self.assertTrue(res.sat)
        self.assertTrue(res.model.get('emergency'), "Emergency flag should be enabled to satisfy new predicate")
        self.assertLessEqual(res.model.get('x', 0), 5, "x must fail the old check (x > 5)")

    def test_domain_constraints_uint8(self):
        """
        Test that witnesses respect variable bit-widths (uint8).
        Old: val < 250
        New: val < 300
        Domain: val is uint8 (max 255).
        
        The solver should find a witness where:
        1. val < 300 (New holds)
        2. NOT (val < 250) (Old fails) -> val >= 250
        3. 0 <= val <= 255 (uint8 constraint)
        
        It should NOT pick 260, even though 260 < 300, because 260 overflows uint8.
        """
        print("\n--- Running test_domain_constraints_uint8 ---")
        res = self.comp.witness_solve(
            "val < 300", 
            "val < 250",
            domains={"val": DomainSpec(kind="uint", bits=8)}
        )
        
        print(f"SAT: {res.sat}")
        print(f"Model: {res.model}")
        
        self.assertTrue(res.sat)
        val = res.model['val']
        self.assertTrue(250 <= val <= 255, f"Witness {val} is outside valid uint8 range [250, 255]")

if __name__ == '__main__':
    unittest.main()