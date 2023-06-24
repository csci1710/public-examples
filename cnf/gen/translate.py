# Translate (simplified) DIMACS CNF input format to an s-expression
# E.g., run cnfgen --varnames --output php3.cnf php 3 and then run this script on php3.cnf
# IMPORTANT: you must make sure to include `--varnames`, or there will be 
#   no variable mapping present in the input, and this script will be unable
#   to extract semantic information about the variables.

from dataclasses import dataclass
import re

@dataclass
class CNF:
    num_vars: int
    num_clauses: int
    variables: dict[int, str]
    clauses: list[list[int]]

    def pretty_meaning(self, s) -> str:
        '''Convert a varname like "p_{1,2}" into s-expression form'''
        matched = re.findall(r"\d+", s)
        return f'(var {" ".join(matched)})'

    def pretty_literal(self, l) -> str:
        '''Convert a DIMACS literal like "-1" into s-expression form'''
        v = abs(int(l))
        if v not in self.variables.keys(): raise ValueError(f'unknown var: {l}')
        if(l < 0): return f'(not {self.pretty_meaning(self.variables[v])})'
        else: return f'{self.pretty_meaning(self.variables[v])}'

    def __str__(self):
        clauses_str = " "+"\n ".join(["("+" ".join([self.pretty_literal(l) for l in c])+")" for c in self.clauses])
        return f'((p cnf {self.num_vars} {self.num_clauses})\n{clauses_str})'

def process_comment(split_line, variables):
    if len(split_line) < 2: return
    if split_line[1] != 'varname': return
    vid = int(split_line[2])
    vexpand = split_line[3] 
    if vid in variables.keys(): raise ValueError(f'duplicate variable meaning: {vid}')
    variables[vid] = vexpand

def translate(filename) -> CNF:
    cnf_file = open(filename, 'r')
    lines: list[str] = cnf_file.readlines()        
    cnf_file.close()

    clauses: list[list[int]] = []
    variables: dict[int, str] = dict()
    num_vars = None
    num_clauses = None

    for line in lines:
        split_line: list[str] = line.split()        
        if len(split_line) < 1: pass   # resilient to blank lines
        elif split_line[0] == 'c': # a comment
            process_comment(split_line, variables)
        elif split_line[0] == 'p':       # problem declaration
            if len(split_line) != 4: raise ValueError(f'p line had unexpected form: {split_line}')
            if split_line[1] != 'cnf': raise ValueError(f'p line had unexpected form: {split_line}')
            if num_vars != None: raise ValueError(f'saw more than one p line in DIMACS spec: {split_line}')
            num_vars = int(split_line[2])
            num_clauses = int(split_line[3])
        # Otherwise, it's a clause
        elif split_line[-1] != '0': raise ValueError(f'clause should be 0-terminated: {split_line}')
        else: 
            split_line = split_line[:-1]
            clauses.append([int(l) for l in split_line])
    if num_vars == None or num_clauses == None:
        return CNF(0, 0, dict(), [])
    return CNF(num_vars, num_clauses, variables, clauses)

def convert_file(filename):
    result = translate(filename)
    out_filename = filename.split('.')[0] + '.scnf'
    out_file = open(out_filename, 'w')
    out_file.write(str(result))
    out_file.close()
    
if __name__ == '__main__':
    import sys
    if len(sys.argv) > 2: 
        print('''Usage: python3 translate.py [CNF filename]
        Provide a filename to convert only that filename.
        Provide no filename to convert all .cnf files in the directory.
        
        For the moment, this utility just writes the translation to 
        a file with the same name, but with the ".scnf" extension.''')
        exit()
    if len(sys.argv) == 2:
        convert_file(sys.argv[1])
    else:
        import os
        for file in os.listdir("."):
            if file.endswith(".cnf"):
                print(f'Processing: {file}')
                convert_file(file)
    
