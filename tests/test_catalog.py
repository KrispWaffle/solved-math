"""Verify that each result is reachable and its local documentation links resolve."""

from pathlib import Path
import re
import unittest
from urllib.parse import urlsplit


ROOT = Path(__file__).resolve().parents[1]


class CatalogTest(unittest.TestCase):
    def test_all_result_directories_are_indexed(self):
        results = {path.parent.name for path in (ROOT / "results").glob("*/README.md")}
        self.assertTrue(results)
        for index in ("README.md", "CONTENTS.md", "site/index.html"):
            text = (ROOT / index).read_text()
            with self.subTest(index=index):
                self.assertEqual(set(re.findall(r"results/([\w-]+)/README\.md", text)), results)

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
