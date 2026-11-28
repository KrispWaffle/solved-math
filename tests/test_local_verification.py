import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class LocalVerificationTest(unittest.TestCase):
    def test_linked_worktree_verifier_uses_the_dependency_repository(self):
        hook = Path(__file__).resolve().parents[1] / ".githooks" / "pre-push"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            project, linked = root / "project", root / "linked"
            dependency, remote = root / "dependency", root / "remote.git"

            def git(*args, cwd=root, env=None):
                return subprocess.run(
                    ["git", *args], cwd=cwd, env=env, check=True, capture_output=True, text=True
                ).stdout.strip()

            git("init", "--quiet", str(project))
            git("init", "--quiet", str(dependency))
            git("init", "--quiet", "--bare", str(remote))
            (project / ".githooks").mkdir()
            shutil.copy2(hook, project / ".githooks" / "pre-push")
            git("config", "core.hooksPath", ".githooks", cwd=project)
            (project / "scripts").mkdir()
            verifier = project / "scripts" / "verify.sh"
            verifier.write_text(
                '#!/bin/sh\nset -eu\n'
                'test "$(git -C "$TEST_DEPENDENCY" rev-parse --absolute-git-dir)" = "$TEST_DEPENDENCY/.git"\n'
                'cat statement > "$TEST_RECEIPT"\n'
            )
            verifier.chmod(0o755)
            (project / "statement").write_text("committed theorem\n")
            git("add", ".", cwd=project)
            git("-c", "user.name=Test", "-c", "user.email=test@example.org", "commit",
                "--no-gpg-sign", "--quiet", "-m", "Fixture", cwd=project)
            git("worktree", "add", "--quiet", "-b", "topic", str(linked), cwd=project)
            (linked / "statement").write_text("uncommitted draft\n")

            receipt = root / "receipt"
            env = dict(
                os.environ, GIT_DIR=git("rev-parse", "--absolute-git-dir", cwd=linked),
                TEST_DEPENDENCY=str(dependency), TEST_RECEIPT=str(receipt),
            )
            git("push", str(remote), "HEAD:refs/heads/topic", cwd=linked, env=env)
            self.assertEqual(receipt.read_text(), "committed theorem\n")
            self.assertEqual(git("rev-parse", "topic", cwd=remote),
                             git("rev-parse", "HEAD", cwd=linked))
