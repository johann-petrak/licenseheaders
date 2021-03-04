import os
import stat
import shutil
import subprocess
import sys

def run_file(licenseheaders_path, file_path, extra_args=None):
    if (extra_args is None):
        extra_args = []
    subprocess.check_call(
        [sys.executable, licenseheaders_path,
        "-t", "lgpl-v3",
        "-y", "2012-2014",
        "-o", "ThisNiceCompany",
        "-n", "ProjectName",
        "-u", "http://the.projectname.com",
        "-f", file_path] + extra_args
    )

def compare_files(file_name, result_file_path, expected_file_path):
    with open(result_file_path) as f1, open(expected_file_path) as f2:
        for line1, line2 in zip(f1, f2):
            if line1 != line2:
                print(f"File {file_name} content is different from expected")
                return 1
    result_file_permissions = stat.S_IMODE(os.lstat(result_file_path).st_mode)
    expected_file_permissions = stat.S_IMODE(os.lstat(expected_file_path).st_mode)
    if (result_file_permissions != expected_file_permissions):
        return 1
    return 0

def main():
    input_dir = "input"
    expected_dir = "expected"
    result_dir = "result"
    licenseheaders_path = "../licenseheaders.py"
    differences = 0

    if not os.path.exists(result_dir):
        os.makedirs(result_dir)

    file_names = [f for f in os.listdir(input_dir) if os.path.isfile(os.path.join(input_dir, f))]
    for file_name in file_names:
        input_file_path = os.path.join(input_dir, file_name)
        expected_file_path = os.path.join(expected_dir, file_name)
        result_file_path = os.path.join(result_dir, file_name)

        shutil.copyfile(input_file_path, result_file_path)

        extra_args = []
        if not os.access(result_file_path, os.W_OK):
            extra_args += ['--force-overwrite']

        # Run it twice for identifying of removed comments
        run_file(licenseheaders_path, result_file_path, extra_args)
        run_file(licenseheaders_path, result_file_path, extra_args)

        differences += compare_files(file_name, result_file_path, expected_file_path)

    if differences:
        return 1
    else:
        return 0

if __name__ == "__main__":
    sys.exit(main())
