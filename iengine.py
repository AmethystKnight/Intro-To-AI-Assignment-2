import sys
import logic
import utils
import time
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
    try:
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
    except FileNotFoundError:
        return None, None

def main():
    if len(sys.argv) < 3: # if detect incorrect number of arguments
        print("Usage: python main.py <filename> <method>")
        return
    
    filename = sys.argv[1].upper()
    method = sys.argv[2].upper()

    #Determine if the user requires the display of running time of the program
    if len(sys.argv) == 4:
        if(sys.argv[3] == "time"):
            displayTime = True
        else:
            print("Command unrecognized. Please try again.")
            return
        
    kb_clauses, query = parseFile(filename)

    if kb_clauses == None:
        print("The specified file was not found. Please try again.")
        return
    
    # Create knowledge base object and add the clauses into the knowledge base
    kb = PropDefiniteKB()
    for clause in kb_clauses:
        clause = expr(expr_handle_infix_imp(expr_handle_infix_or(clause)))
        kb.tell(clause)

    #Start the counting of program runtime
    start_time = time.time()

    # passes kb and query onto specific method based on whether we are using truth table or other
    if method == 'TT':
        result, models = logic.tt_entails(kb, expr(query)) 
    elif method == 'FC':
        result, symbolsFC =  pl_fc_entails(kb, expr(query))
    elif method == 'BC':
        result, symbolsBC = pl_bc_entails(kb, expr(query))
    else:
        print("Invalid method specified.")
        return

    #Record the time when a result is returned by the algorithm
    end_time = time.time()

    #Calculate the elapsed time
    elapsed_time = (end_time - start_time) * 1000

    # displays result based on the chosen algorithm
    print("Result:")
    if result:
        if method == 'TT':
            # with the top level loop checking if result is true, we can assume that TT returned true.
            print("YES:", models)
        elif method == 'FC':
            print("Yes: " + ' '.join(map(str, symbolsFC)))
        elif method == 'BC':
            print("Yes: " + ' '.join(map(str, symbolsBC)))
    else:
        print("No")

    if displayTime:
        print("Time taken: " + "{:.3f}".format(elapsed_time) + "ms;")
if __name__ == "__main__":
    main()
