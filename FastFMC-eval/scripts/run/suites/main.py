import os

TOOLS = ['FastFMC', 'ddnnife', 'd4-query', 'query-ddnnf', 'Ganak', 'sharpSAT', 'countAntom']


def run(r, args):
    for t in (args.tools or TOOLS):
        r.run_tool(t, args.runs, t, prefix=None)
