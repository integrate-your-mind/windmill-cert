from __future__ import annotations

import unittest

from scripts.audit_lean import audit_sources


class LeanAuditTests(unittest.TestCase):
    def test_trusted_lean_sources_have_no_trust_holes(self) -> None:
        self.assertEqual(audit_sources(), [])


if __name__ == "__main__":
    unittest.main()
