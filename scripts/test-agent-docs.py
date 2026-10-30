#!/usr/bin/env python3
"""Regression cases for repository-wide documentation discovery and references."""

from pathlib import Path
import subprocess
import tempfile
import unittest

from doc_refs import anchors, local_references, prose, source_files


class DocumentationTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="vcvio-doc-refs-")
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def test_nested_inventory_and_canonical_symlink(self):
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        self.write(".gitignore", ".lake/\n")
        expected = [self.write("AGENTS.md", "guide"),
                    self.write("Interop/Backend/README.md", "guide"),
                    self.write("VCVioComplexity/PROVENANCE.md", "guide")]
        (self.root / "CLAUDE.md").symlink_to("AGENTS.md")
        self.write("third_party/vendor/README.md", "external")
        self.write(".lake/packages/README.md", "ignored")
        self.assertEqual(source_files(self.root, "*.md"), sorted(expected))

    def test_links_anchors_and_reference_definitions(self):
        self.write("docs/target.md", "# Shared `API`\n## Same\n## Same\n<a id='manual'></a>\n")
        doc = self.write("docs/nested/README.md",
                         "[api](../target.md#shared-api)\n[x][ref]\n"
                         "[ref]: ../target.md#same-1\n[m](../target.md#manual)\n")
        self.assertEqual(local_references(self.root, doc), [])
        doc.write_text("[bad](../target.md#removed)\n[missing]: ../gone.md\n")
        errors = local_references(self.root, doc)
        self.assertEqual(len(errors), 2)
        self.assertIn("missing anchor", errors[0])
        self.assertIn("missing link target", errors[1])

    def test_source_comments_and_all_library_roots(self):
        self.write("HashSig/Present.lean", "module\n")
        doc = self.write("VCVio/Proof.lean",
                         'def text := "HashSig/Absent.lean /- not a comment -/"\n'
                         '/-! See `HashSig/Absent.lean`. /- nested -/ -/\n')
        errors = local_references(self.root, doc)
        self.assertEqual(len(errors), 1)
        self.assertIn("Proof.lean:2:", errors[0])
        self.assertNotIn("not a comment", prose(doc))

    def test_relative_links_are_not_checked_again_as_root_paths(self):
        self.write("docs/root.md", "# Root\n")
        self.write("Interop/Cryptol/docs/model.md", "# Model\n")
        doc = self.write("Interop/Cryptol/README.md", "[model](docs/model.md#model)\n"
                         "[reference]: docs/model.md\n")
        self.assertEqual(local_references(self.root, doc), [])
        doc.write_text("[model](docs/missing.md)\n")
        errors = local_references(self.root, doc)
        self.assertEqual(len(errors), 1)
        self.assertIn("missing link target", errors[0])

    def test_plans_and_pinned_sources_do_not_hide_broken_links(self):
        self.write("VCVio/Present.lean", "module\n")
        doc = self.write("docs/history.md", "Status: historical record.\n"
                         "`VCVio/Gone.lean`\n[missing](gone.md)\n")
        self.assertEqual(len(local_references(self.root, doc)), 1)
        doc.write_text("The planned `VCVio/Future.lean` belongs here.\n"
                       "[past](https://example.org/commit/VCVio/Gone.lean)\n")
        self.assertEqual(local_references(self.root, doc), [])

    def test_fenced_headings_are_not_anchors(self):
        self.assertEqual(anchors("# Visible\n```lean\n# Hidden\n```\n"), {"visible"})


if __name__ == "__main__":
    unittest.main()
