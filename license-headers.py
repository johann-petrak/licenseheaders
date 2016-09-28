#!/usr/bin/env python
# encoding: utf-8

"""A tool to change or add license headers in all supported files in or below a directory."""

# Copyright (c) 2016 Johann Petrak
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

from __future__ import unicode_literals
from __future__ import print_function


import os
import shutil
import sys
import logging
import argparse
import re
import fnmatch
from string import Template
import io
import subprocess


__version__ = '0.1'  
__author__ = 'Johann Petrak'
__license__ = 'MIT'


log = logging.getLogger(__name__)


try:
    unicode
except NameError:
    unicode = str


## all filename pattherns of files we know how to process
patterns = ["*.java","*.scala","*.groovy","*.jape"]

## how each file extension maps to a specific processing type
processingTypes = {
        "java": "java",
        "scala": "java",
        "groovy": "java",
        "jape": "java"
    }

## for each processing type, the detailed settings of how to process files of that type
typeSettings = {
    "java": {
        "headerStartPattern": "/*",  ## used to find the beginning of a header bloc
        "headerEndPattern": "*/",    ## used to find the end of a header block
        "headerStartLine": "/*\n",   ## inserted before the first header text line
        "headerEndLine": " */\n",    ## inserted after the last header text line
        "linePrefix": " * ",         ## inserted before each header text line
        "lineSuffix": "",            ## inserted after each header text line, but before the new line
    }
}

def parse_command_line(argv):
    """Parse command line argument. See -h option.

    Arguments:
      argv: arguments on the command line must include caller file name.

    """
    import textwrap

    example = textwrap.dedent("""
      ## Some examples of how to use this command!
    """).format(os.path.basename(argv[0]))
    formatter_class = argparse.RawDescriptionHelpFormatter
    parser = argparse.ArgumentParser(description="Python license header updater",
                                     epilog=example,
                                     formatter_class=formatter_class)
    parser.add_argument("-V", "--version", action="version",
                        version="%(prog)s {}".format(__version__))
    parser.add_argument("-v", "--verbose", dest="verbose_count",
                        action="count", default=0,
                        help="increases log verbosity (can be specified "
                        "multiple times)")
    parser.add_argument("-d", "--dir", dest="dir", nargs=1,
                        help="The directory to recursively process.")
    parser.add_argument("-t", "--tmpl", dest="tmpl", nargs=1,
                        help="Template name or file to use.")
    parser.add_argument("-y", "--years", dest="years", nargs=1,
                        help="Year or year range to use.")
    parser.add_argument("-o", "--owner", dest="owner", nargs=1,
                        help="Name of copyright owner to use.")
    parser.add_argument("-n", "--projname", dest="projectname", nargs=1,
                        help="Name of project to use.")
    parser.add_argument("-u", "--projurl", dest="projecturl", nargs=1,
                        help="Url of project to use.")
    arguments = parser.parse_args(argv[1:])

    # Sets log level to WARN going more verbose for each new -V.
    log.setLevel(max(3 - arguments.verbose_count, 0) * 10)
    return arguments


def get_paths(patterns, start_dir="."):
    """Retrieve files that match any of the glob patterns from the start_dir and below."""
    for root, dirs, files in os.walk(start_dir):
        names = []
        for pattern in patterns:
            names += fnmatch.filter(files, pattern)
        for name in names:
            path = os.path.join(root, name)
            yield path

## return an array of lines, with all the variables replaced
## throws an error if a variable cannot be replaced
def read_template(templateFile,dict):
    with open(templateFile,'r') as f:
        lines = f.readlines()
    lines = [Template(line).substitute(dict) for line in lines]  ## use safe_substitute if we do not want an error
    return lines

def main():
    """Main function."""
    logging.basicConfig(stream=sys.stderr, level=logging.DEBUG)
    try:
        error = False
        settings = {
        }
        templateLines = None
        arguments = parse_command_line(sys.argv)
        if arguments.dir:
            start_dir = arguments.dir[0]
        else:
            start_dir = "."
        if arguments.years:
            settings["years"] = arguments.years[0]
        if arguments.owner:
            settings["owner"] = arguments.owner[0]
        if arguments.projectname:
            settings["projectname"] = arguments.projectname[0]
        if arguments.projecturl:
            settings["projecturl"] = arguments.projecturl[0]
        ## if we have a template name specified, try to get or load the template
        if arguments.tmpl:
            opt_tmpl = arguments.tmpl[0]
            ## first get all the names of our own templates
            ## for this get first the path of this file
            templatesDir = os.path.join(os.path.dirname(os.path.abspath(__file__)),"templates")
            ## get all the templates in the templates directory
            templates = [f for f in get_paths("*.tmpl",templatesDir)]
            templates = [(os.path.splitext(os.path.basename(t))[0],t) for t in templates]
            ## filter by trying to match the name against what was specified
            tmpls = [t for t in templates if opt_tmpl in t[0]]
            if len(tmpls) == 1:
                tmplName = tmpls[0][0]
                tmplFile = tmpls[0][1]
                print("Using template ",tmplName)
                templateLines = read_template(tmplFile,settings)
            else:
                if len(tmpls) == 0:
                    ## check if we can interpret the option as file
                    if os.path.isfile(opt_tmpl):
                        print("Using file ",os.path.abspath(opt_tmpl))
                        templateLines = read_template(os.path.abspath(opt_tmpl),settings)
                    else:
                        print("Not a built-in template and not a file, cannot proceed: ",opt_tmpl)
                        error = True
                else:
                    ## notify that there are multiple matching templates
                    print("There are multiple matching template names: ",[t[0] for t in tmpls])
                    error = True
        else: # no tmpl parameter
            if not arguments.years:
                print("No template specified and no years either, nothing to do")
                error = True
        if not error:
            logging.debug("Got template lines: ",templateLines)
            ## now do the actual processing: if we did not get some error, we have a template loaded or no template at all
            ## if we have no template, then we will have the years.
            ## now process all the files and either replace the years or replace/add the header
            print("Processing directory ",start_dir)
            for file in get_paths(patterns,start_dir):
                print("Processing file: ",file)
                ## 
    finally:
        logging.shutdown()


if __name__ == "__main__":
    sys.exit(main())
