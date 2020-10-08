#!/usr/bin/env python3
import json
import os
import subprocess

def run_in_dir(working_dir, cmdline):
    old_working_dir = os.getcwd()
    os.chdir(working_dir)
    try:
        completed = subprocess.run(cmdline, capture_output=True)
        return completed.stdout.decode("utf-8")
    finally:
        os.chdir(old_working_dir)


def run_tests(working_dir, program, subset):
    cmdline = ["dune", "exec", "--", program, "test", "--color=never", "--json", subset]
    output = run_in_dir(working_dir, cmdline)
    json_output = "".join(output.splitlines()[3:])
    results = json.loads(json_output)
    return (results["success"], results["failures"])

class Res(object):
    def __init__(self, total, failed):
        self.total = total
        self.failed = failed
        self.passed = total - failed

def tally_tests(working_dir, program, subset):
    total, failed = run_tests(working_dir, program, subset)
    return Res(total, failed)

def main(petr4_repo_root):
    frontend_root = os.path.join(petr4_repo_root, "test")
    print("Running test suite. This will take a few minutes...")
    parser_res      = tally_tests(frontend_root, "./test.exe", "parser tests")
    typechecker_res = tally_tests(frontend_root, "./test.exe", "typecheck tests")
    excl_res        = tally_tests(frontend_root, "./test.exe", "excluded")
    p4c_stf_res     = tally_tests(petr4_repo_root, "bin/test.exe", "p4c stf tests")
    custom_stf_res  = tally_tests(petr4_repo_root, "bin/test.exe", "petr4 stf tests")
    excl_stf        = tally_tests(petr4_repo_root, "bin/test.exe", "excluded tests")
    output = """
{parser_res.total} parser tests
    {parser_res.passed} passed
    {parser_res.failed} failed
{typechecker_res.total} typechecker tests
    {typechecker_res.passed} passed
    {typechecker_res.failed} failed [See logs in TODO FILL IN PATH.]
{p4c_stf_res.total} p4c STF tests
    {p4c_stf_res.passed} passed
    {p4c_stf_res.failed} failed
{custom_stf_res.total} custom STF tests
    {custom_stf_res.passed} passed
    {custom_stf_res.failed} failed
{excl_res.total} excluded [See examples/checker_tests/excluded.]
    {excl_stf.total} with STF
    """.format(parser_res=parser_res, typechecker_res=typechecker_res,
               p4c_stf_res=p4c_stf_res, custom_stf_res=custom_stf_res,
               excl_res=excl_res, excl_stf=excl_stf)
    print(output)

if __name__ == "__main__":
    from os.path import abspath, dirname
    script_path = abspath(__file__)
    petr4_root = dirname(dirname(script_path))
    main(petr4_root)
