#!/usr/bin/env python
# encoding: utf-8

"""A tool to change or add license headers in all supported files in or below a directory."""

#!/usr/bin/env python
# encoding: utf-8
"""A tool to change or add license headers in all supported files in or below a directory."""


import os
import sys
import argparse
import fnmatch
import logging
from shutil import copyfile
from string import Template
import toml

import regex
import re

# set up the root logger
LOGGING_FORMAT = "%(asctime)s|%(levelname)s|%(name)s|%(message)s"
logging.basicConfig(stream=sys.stderr, format=LOGGING_FORMAT, level=logging.WARN)
LOGGER = logging.getLogger(__name__)
LOGGER.setLevel(logging.WARNING)


def merge_configs(target_config, to_add):
    """
    Replace all top-level settings except when a key starts with "update_" in which case
    there must be a top level setting to update which is a dictionary and that dictionary
    gets updated recursively. This updates the first argument in place (and all recursive
    dictionaries) and returns the first argument.

    :param target_config: the dictionary/config to update
    :param to_add: a dictionary of items to replace or update
    :return: the modified target dictionary/config
    """
    for k,v in to_add.items():
        if k.startswith("update_"):
            korig = k
            k = k[7:]
            if k not in target_config:
                raise Exception(f"Cannot use {korig}, {k} not in existing config")
            val = target_config[k]
            if not isinstance(val, dict):
                raise Exception(f"Cannot use {korig}, {k} is not a structured config")
            if not isinstance(v, dict):
                raise Exception(f"Cannot use {korig}, value is not a structured config")
            merge_configs(val, v)
        else:
            target_config[k] = v
    return target_config


# class for dict args. Use --argname key1=val1,val2 key2=val3 key3=val4, val5
class DictArgs(argparse.Action):
    def __call__(self, parser, namespace, values, option_string=None):
        dict_args = {}
        if not isinstance(values, (list,)):
            values = (values,)
        for value in values:
            n, v = value.split("=")
            if v and "," in str(v):
                dict_args[n] = v.split(",")
            else:
                dict_args[n] = list()
                dict_args[n].append(str(v).strip())
        setattr(namespace, self.dest, dict_args)

def parse_command_line(sysargs=None):
    """
    Parse command line arguments or the arguments passed on explicitly.

    :param argv: None to use the command line args or a list of args to use instead.
    :return: parsed arguments
    """
    import textwrap

    config_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "config.toml")
    epilog = textwrap.dedent(f"""
    
    Default config file: {config_path}
    """)
    parser = argparse.ArgumentParser(
        description="License header adder/updater/remover",
        epilog=epilog,
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("filesordirs", nargs="+", type=str,
                        help="Files or directories to process")
    parser.add_argument("-a", "--action", type=str, default="ensure",
                        help="Action, one of remove, ensure, check (ensure)")
    parser.add_argument("-c", "--config", default=None, type=str,
                        help="Additional config file to use")
    parser.add_argument("-l", "--loglvl", default="warn", type=str,
                        help="Logging level to use, one of debug, info, warn, error (warn)")
    # command line arguments to update the config
    parser.add_argument("-t", "--tmpl", default=None, type=str,
                        help="Config: Template name or file path (if the path contains a dot)")
    parser.add_argument("-y", "--years", default=None, type=str,
                        help="Config: Variable year or years to use")
    parser.add_argument("--vars", "--variables", default=None, nargs="+",
                        help="Set template vars as a list of varname=value specifications",
                        action=DictArgs)
    # Normally all types specified in the config file(s) are processed, if this is specified, only the
    # given types are specified
    parser.add_argument("--types", default=None, type=str, nargs="+",
                        help="Config: types to process")
    # Normally all files that have extensions known from the config are processed for all configured types
    # if this is specified, only the given extensions are used
    parser.add_argument("--exts", default=None, nargs="+",
                        help="List of file extensions (without dot) to use")
    parser.add_argument("--dry", action="store_true",
                        help="If specified, does not modify any files but reports what it would be doing")
    return parser.parse_args(sysargs)


def main(sysargs=None):
    args = parse_command_line(sysargs=sysargs)
    LOGGER.setLevel(args.loglvl.upper())

    # locate and read the default config file for the package
    config_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "config.toml")
    LOGGER.info(f"Loading default configuration file {config_path}")
    config = toml.load(config_path)
    LOGGER.debug(f"Got default config: {config}")

    # try to locate a local config file
    if os.path.exists(".licenseheaders.toml"):
        LOGGER.info(f"Loading configuration file .licenseheaders.toml")
        local_config = toml.load(".licenseheaders.toml")
        LOGGER.debug(f"Got local config: {local_config}")
        merge_configs(config, local_config)

    if args.config is not None:
        LOGGER.info(f"Loading configuration file {args.config}")
        use_config = toml.load(args.config)
        LOGGER.debug(f"Got additional config: {use_config}")
        merge_configs(config, use_config)

    if args.years is not None:
        config["variables"]["years"] = args.years

    config_args = vars(args)
    LOGGER.info(f"config_args={config_args}")
    for k in ["tmpl", "types", "years"]:
        v = config_args.get(k)
        if v is not None:
            LOGGER.info(f"Setting {k} to {v}")
            config[k] = v
    if args.vars:
        config["variables"].update(args.vars)
    LOGGER.debug(f"Final config: {config}")

    encoding = config["encoding"]
    # make sure we know which template to use
    if "tmpl" not in config:
        raise Exception("No template configured, use 'tmpl' config!")
    # check that template actually exists
    tmpl_name = config["tmpl"]
    if "." in tmpl_name:
        with open(tmpl_name, "rt", encoding=encoding) as infp:
            tmpl_str = infp.read()
    else:
        # we want a template from the config
        tmpls = config.get("templates", {})
        tmpl_str = tmpls.get(tmpl_name)
        if tmpl_str is None:
            raise Exception(f"No template {tmpl_name} defined in the configuration in [templates]")
    # find all the variables in the template and make sure we have values for them
    varnames = []
    for f1, f2, f3, f4 in re.findall(Template.pattern, tmpl_str):
        name = f2 or f3
        if name:
            varnames.append(name)
    LOGGER.info(f"Template variable names: {','.join(varnames)}")
    config_vars = config.get("variables", {})
    for varname in varnames:
        if varname not in config_vars:
            raise Exception(f"Variable {varname} not in configuration in [variables]")

    # get all the supported types, make sure there is at least one
    # also remember which type to use for which extension and make sure there is not more than one type
    # defined per extension
    config_typedict = config.get("type", {})
    if len(config_typedict) == 0:
        raise Exception("No type definitions in configuration, add at least one like [type.java]")

    ext2type = {}
    # get all known types
    l_types = set()
    for ctype_name, ctype_def in config_typedict.items():
        l_types.add(ctype_name)
        tmp_exts = ctype_def.get("extensions", [])
        for tmp_ext in tmp_exts:
            if tmp_ext in ext2type:
                raise Exception(f"Extension {tmp_ext} defined for {ext2type[tmp_ext]} and {ctype_name}")
            ext2type[tmp_ext] = ctype_name

    known_types = sorted(list(l_types))
    LOGGER.info(f"Known types: {known_types}")

    # process the configured list of types to process
    if args.types:
        config["types"] = args.types
    config_typelist = config.get("types")
    if config_typelist is not None:
        for ctype_name in config_typelist:
            if ctype_name not in l_types:
                raise Exception(f"Configured type {ctype_name} not in known types {known_types}")
    else:
        config_typelist = known_types

    l_extensions = set()
    for ctype_name in config_typelist:
        ctype_def = config["type"][ctype_name]
        l_extensions.update(ctype_def.get("extensions", []))
    known_extensions = sorted(list(l_extensions))
    LOGGER.info(f"Known extensions for used types: {known_extensions}")

    if args.exts:
        config["exts"] = args.exts
    config_extlist = config.get("exts")

    if config_extlist is not None:
        for cext in config_extlist:
            if cext not in l_extensions:
                raise Exception(f"Configured extensions {cext} not in known extensions {known_extensions}")
    else:
        config_extlist = known_extensions

    LOGGER.info(f"List of extensions to use: {config_extlist}")

    # No process all the fileordirs on the command line
    # if it is a file, process it immediately:
    #   if we can determine the type, use the determined type
    #   otherwisem, expect only one type in config_typelist, if more, error
    # otherwise, if it is a directory, walk all the files in the directory recursively
    #   for each file, determine the type to use to process it
    #   if we can determine a type, check if the file is in the ignore list
    #   if not ignored and we have a type, process it
    # "process it" means:
    #   read in the whole file (we assume whole file fits into memory easily)
    #   perform the action or do nothing, if action performed we have a modified file
    #   if we performed the action:
    #      backup or inform that we would back up
    #      write modified or inform that we would write modified

if __name__ == "__main__":
    main()
