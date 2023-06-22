# Translate (simplified) DIMACS CNF input format to an s-expression
# E.g., run cnfgen --output php3.cnf php 3 and then run this script on php3.cnf
from dataclasses import dataclass


@dataclass
class CNF:
    num_vars: int
    num_clauses: int
    clauses: list[list[int]]

    def __str__(self):        
        return f'((p cnf {self.num_vars} {self.num_clauses}) {"".join(["".join([str(l) for l in c]) for c in self.clauses])})'

def translate(filename) -> CNF:
    cnf_file = open(filename, 'r')
    lines: list[str] = cnf_file.readlines()        
    cnf_file.close()

    clauses = []
    num_vars = None
    num_clauses = None

    for line in lines:
        split_line: list[str] = line.split()        
        if len(split_line) < 1: pass   # resilient to blank lines
        elif split_line[0] == 'c': pass  # a comment
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
            clauses.append('('+' '.join(split_line)+")")
    if num_vars == None or num_clauses == None:
        return CNF(0, 0, [])        
    return CNF(num_vars, num_clauses, clauses)

if __name__ == '__main__':
    import sys
    if len(sys.argv) != 2: # usual first arg is the name of the script
        print("Usage: python3 translate.py <CNF filename>")
        exit()
    result = translate(sys.argv[1])
    out_filename = sys.argv[1].split('.')[0] + '_t.cnf'
    out_file = open(out_filename, 'w')
    out_file.write(str(result))
    out_file.close()
    
