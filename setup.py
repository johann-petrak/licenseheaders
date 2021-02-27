#!/usr/bin/env python
# encoding: utf-8

"""Packaging script."""

import sys
import os
import re
from setuptools import setup

if sys.version_info < (3, 7):
    sys.exit("ERROR: gatenlp requires Python 3.7+")

here = os.path.abspath(os.path.dirname(__file__))
with open(os.path.join(here, "README.md")) as f:
    readme = f.read()


def versionfromfile(*filepath):
    here = os.path.abspath(os.path.dirname(__file__))
    infile = os.path.join(here, *filepath)
    with open(infile) as fp:
        version_match = re.search(r"^__version__\s*=\s*['\"]([^'\"]*)['\"]",
                                  fp.read(), re.M)
        if version_match:
            return version_match.group(1)
        raise RuntimeError("Unable to find version string in {}.".format(infile))


version = versionfromfile("licenseheaders/version.py")

setup(
    name="licenseheaders",
    version=version,
    author="Johann Petrak",
    author_email="johann.petrak@gmail.com",
    description='Add or change license headers for all files in a directory',
    long_description=readme,
    long_description_content_type="text/markdown",
    setup_requires=[],
    install_requires=["regex", "toml"],
    python_requires=">=3.7",
    license="MIT",
    keywords="",
    url="http://github.com/johann-petrak/licenseheaders",
    package_dir={"licenseheaders":"licenseheaders"},
    package_data={'licenseheaders': ['config.toml']},
    entry_points={'console_scripts': ['licenseheaders=licenseheaders.licenseheaders:main']},
    test_suite='tests',
    classifiers=["Development Status :: 5 - Production/Stable",
                 "License :: OSI Approved :: MIT License",
                 "Environment :: Console",
                 "Natural Language :: English",
                 "Programming Language :: Python :: 3.7",
                 "Programming Language :: Python :: 3.8",
                 "Programming Language :: Python :: 3.9",
                 "Topic :: Software Development",
                 "Topic :: Software Development :: Code Generators",
                 "Intended Audience :: Developers",
                ],
)
