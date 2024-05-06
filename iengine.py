import sys
import logic
import utils
from utils import expr
from logic import PropDefiniteKB, expr_handle_infix_imp, expr_handle_infix_or, pl_fc_entails, pl_bc_entails

"""
Usage: 
Command: python iengine.py <filename> <method>
I.e: python iengine.py test1.txt FC
I.e: python iengine.py test_HornKB.txt TT
"""

# reads file and extracts info like the knowledge base and the query 
def parseFile(filename):
    with open(filename, 'r') as file: # reading the file
        content = file.read()
    
    # splitting the input file to find which bit is the knowledge base and which bit is the query
    parts = content.split('TELL')
    tell_section = parts[1].split('ASK')
    
    kb_raw = tell_section[0].strip()
    query_raw = tell_section[1].strip()

    kb_clauses = [clause.strip() for clause in kb_raw.split(';') if clause.strip()]
    query = query_raw.strip()
    
    return kb_clauses, query

def main():
    if len(sys.argv) < 3: # if detect incorrect number of arguments
        print("Usage: python main.py <filename> <method>")
        return
    
    resultFC = False
    resultBC = False
    filename = sys.argv[1].upper()
    method = sys.argv[2].upper()
    kb_clauses, query = parseFile(filename)

    #Create knowledge base object and add the clauses into the knowledge base
    kb = PropDefiniteKB()
    for clause in kb_clauses:
        clause = expr(expr_handle_infix_imp(expr_handle_infix_or(clause)))
        kb.tell(clause)

    # passes kb and query onto specific method based on whether we are using truth table or other
    # these need to be updated cuz logic.py uses different names for TruthTable etc
    if method == 'TT':
        result = logic.tt_entails(kb, expr(query)) # returns true/false
    elif method == 'FC':
        result, symbolsFC =  pl_fc_entails(kb, expr(query))
    elif method == 'BC':
        result, symbolsBC = pl_bc_entails(kb, expr(query))
    else:
        print("Invalid method specified.")
        return

    # displays result based on the chosen algorithm
    print("Result:")
    if result:
        if method == 'TT':
            print("Yes") # with the top level loop checking if result is true, we can assume that TT returned true.
        elif method == 'FC':
            print("Yes: " + ' '.join(map(str, symbolsFC)))
        elif method == 'BC':
            print("Yes: " + ' '.join(map(str, symbolsBC)))
    else:
        print("No\n")

if __name__ == "__main__":
    main()
