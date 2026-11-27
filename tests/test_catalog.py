"""Verify that each result is reachable and its local documentation links resolve."""

from pathlib import Path
import re
import unittest
from urllib.parse import urlsplit


ROOT = Path(__file__).resolve().parents[1]


class CatalogTest(unittest.TestCase):
    def test_results_and_archived_manuscripts_are_indexed(self):
        results = {p.relative_to(ROOT).as_posix() for p in (ROOT / "results").glob("*/README.md")}
        archive = {p.relative_to(ROOT).as_posix() for p in (ROOT / "archive").glob("*/README.md")}
        self.assertTrue(results)
        for index, expected in (
            ("README.md", results),
            ("CONTENTS.md", results | archive),
            ("site/index.html", results | archive),
        ):
            text = (ROOT / index).read_text()
            with self.subTest(index=index):
                links = re.findall(r"(?:results|archive)/[\w-]+/README\.md", text)
                self.assertEqual(set(links), expected)

    def test_relative_links(self):
        for document in ROOT.rglob("*.md"):
            if {".lake", ".git"}.intersection(document.relative_to(ROOT).parts):
                continue
            for link in re.findall(r"\[[^\]\n]+\]\(([^)\s]+)\)", document.read_text()):
                target = urlsplit(link)
                if target.scheme or target.netloc or not target.path:
                    continue
                with self.subTest(document=str(document.relative_to(ROOT)), link=link):
                    self.assertTrue((document.parent / target.path).is_file())


if __name__ == "__main__":
    unittest.main()
