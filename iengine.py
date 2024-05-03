import sys
from logic import TruthTable, ForwardChaining, BackwardChaining

"""
Usage: 
Command: python iengine.py <filename> <method>
I.e: python iengine.py test1.txt FC
I.e: python iengine.py test_HornKB TT
"""

def main():
    if len(sys.argv) < 3:
        print("Usage: python main.py <filename> <method>")
        return
    
    filename = sys.argv[1]
    method = sys.argv[2]
    kb, query = parseFile(filename)

    # these need to be updated cuz logic.py uses different names for TruthTable etc
    if method == 'TT':
        result = TruthTable(kb, query)
    elif method == 'FC':
        result = ForwardChaining(kb, query)
    elif method == 'BC':
        result = BackwardChaining(kb, query)
    else:
        print("Invalid method specified.")
        return

    print("Result:", result)

if __name__ == "__main__":
    main()



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
