#!/usr/bin/env python
# encoding: utf-8

"""Packaging script."""

import os
import re
import glob
from setuptools import setup, find_packages

here = os.path.abspath(os.path.dirname(__file__))
readme = open(os.path.join(here, 'README.md')).read()

def versionfromfile(*filepath):
    here = os.path.abspath(os.path.dirname(__file__))
    infile = os.path.join(here, *filepath)
    with open(infile) as fp:
        version_match = re.search(r"^__version__\s*=\s*['\"]([^'\"]*)['\"]",
                                  fp.read(), re.M)
        if version_match:
            return version_match.group(1)
        raise RuntimeError("Unable to find version string in {}.".format(infile))
setup(
    name="licenseheaders",
    version=versionfromfile("licenseheaders.py"),
    author="Johann Petrak",
    author_email="johann.petrak@gmail.com",
    description='Add or change license headers for all files in a directory',
    long_description=readme,
    long_description_content_type="text/markdown",
    setup_requires=[],
    install_requires=["regex"],
    python_requires=">=3.5",
    license="MIT",
    keywords="",
    url="http://github.com/johann-petrak/licenseheaders",
    py_modules=['licenseheaders'],
    # packages=["licenseheaders"],
    # package_dir={"licenseheaders":"licenseheaders"},
    # package_data={'licenseheaders': ['templates/*']},
    include_package_data=True,
    entry_points={'console_scripts': ['licenseheaders=licenseheaders:main']},
    data_files=[("templates", glob.glob("templates/*.tmpl"))],
    # test_suite='tests',
    # tests_require=['mock'],
    classifiers=["Development Status :: 5 - Production/Stable",
                 "License :: OSI Approved :: MIT License",
                 "Environment :: Console",
                 "Natural Language :: English",
                 "Programming Language :: Python :: 3",
                 "Topic :: Software Development",
                 "Topic :: Software Development :: Code Generators",
                 "Intended Audience :: Developers",
                ],
)
