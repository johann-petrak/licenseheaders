import os
import stat
import shutil
import sys
import unittest
import licenseheaders
import tempfile
from pathlib import Path

TEST_FILE = Path(__file__)
TEST_DIR = TEST_FILE.parent


def run_file(file_path, extra_args=None):
    if (extra_args is None):
        extra_args = []
    # HACK to avoid refactoring elsewhere
    orig_argv = sys.argv
    sys.argv = [
        "licenseheaders", "-t", "lgpl-v3", "-y",
        "2012-2014", "-o", "ThisNiceCompany", "-n", "ProjectName", "-u",
        "http://the.projectname.com", "-f", file_path
    ] + extra_args
    licenseheaders.main()
    sys.argv = orig_argv


def compare_files(file_name, result_file_path, expected_file_path):
    with open(result_file_path) as f1, open(expected_file_path) as f2:
        for line1, line2 in zip(f1, f2):
            if line1 != line2:
                print(f"File {file_name} content is different from expected")
                return 1
    result_file_permissions = stat.S_IMODE(os.lstat(result_file_path).st_mode)
    expected_file_permissions = stat.S_IMODE(
        os.lstat(expected_file_path).st_mode)
    if (result_file_permissions != expected_file_permissions):
        return 1
    return 0


class TestLicenseHeaders(unittest.TestCase):

    @classmethod
    def setUpClass(cls) -> None:
        """
        Create a directory for results.
        """
        cls.input_dir = TEST_DIR / "input"
        cls.expected_dir = TEST_DIR / "expected"
        cls.result_dir = TEST_DIR / "result"

    def test_licenseheaders(self):
        """
        Check that adding licenses to known inputs matches expectations.
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            file_names = [
                f for f in os.listdir(self.input_dir)
                if os.path.isfile(os.path.join(self.input_dir, f))
            ]
            for file_name in file_names:
                input_file_path = os.path.join(self.input_dir, file_name)
                expected_file_path = os.path.join(self.expected_dir, file_name)
                result_file_path = os.path.join(tmpdir, file_name)

                shutil.copyfile(input_file_path, result_file_path)

                extra_args = []
                if not os.access(result_file_path, os.W_OK):
                    extra_args += ['--force-overwrite']

                # Run it twice for identifying of removed comments
                run_file(result_file_path, extra_args)
                run_file(result_file_path, extra_args)

                difference = compare_files(file_name, result_file_path,
                                             expected_file_path)
                self.assertEqual(difference, 0)


if __name__ == "__main__":
    unittest.main()
