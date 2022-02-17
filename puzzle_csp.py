#Look for #IMPLEMENT tags in this file.
'''
All models need to return a CSP object, and a list of lists of Variable objects 
representing the board. The returned list of lists is used to access the 
solution. 

For example, after these three lines of code

    csp, var_array = caged_csp_model(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

var_array[0][0].get_assigned_value() should be the correct value in the top left
cell of the FunPuzz puzzle.

The grid-only models do not need to encode the cage constraints.

1. binary_ne_grid (worth 10/100 marks)
    - A model of a FunPuzz grid (without cage constraints) built using only 
      binary not-equal constraints for both the row and column constraints.

2. nary_ad_grid (worth 10/100 marks)
    - A model of a FunPuzz grid (without cage constraints) built using only n-ary 
      all-different constraints for both the row and column constraints. 

3. caged_csp_model (worth 25/100 marks) 
    - A model built using your choice of (1) binary binary not-equal, or (2) 
      n-ary all-different constraints for the grid.
    - Together with FunPuzz cage constraints.

'''
from cspbase import *
import itertools

def binary_ne_grid(fpuzz_grid):
    
    # get dimensions 
    n = fpuzz_grid[0][0]
    domain = range(1,n+1)
    
    # create vars
    vars = [[Variable(str(i*10+j), domain) for i in domain] for j in domain]

    csp = CSP('binary', [var for row in vars for var in row])
    permutations= list(itertools.permutations(domain, 2))
    
    for i in range(n):
        row = vars[i]
        for pair in itertools.combinations(row, 2):
            c = Constraint('Row-{0}-{1}'.format(pair[0].name,pair[1].name), pair)
            c.add_satisfying_tuples(permutations)
            csp.add_constraint(c)
            
        col = [var[i] for var in vars]
        for pair in itertools.combinations(col, 2):
            c = Constraint('Col-{0}-{1}'.format(pair[0].name,pair[1].name), pair)
            c.add_satisfying_tuples(permutations)
            csp.add_constraint(c)
            
    return csp, vars

        
def nary_ad_grid(fpuzz_grid):

    # get dimensions 
    n = fpuzz_grid[0][0]
    domain = range(1,n+1)
    
    # create vars
    vars = [[Variable(str(i*10+j), domain) for i in domain] for j in domain]

    csp = CSP('n-ary', [var for row in vars for var in row])
    permutations = list(itertools.permutations(domain))
    
    for i in range(n):
        c_row = Constraint('Row-{}'.format(i+1), vars[i])
        c_row.add_satisfying_tuples(permutations)
        csp.add_constraint(c_row)
        
        c_col = Constraint('Col-{}'.format(i+1), [var[i] for var in vars])
        c_col.add_satisfying_tuples(permutations)
        csp.add_constraint(c_col)
        
    return csp, vars

    
fpuzz_grid = [[3],[11,21,3,0],[12,22,2,1],[13,23,33,6,3],[31,32,5,0]]


def caged_csp_model(fpuzz_grid):
    ##IMPLEMENT 
    csp, vars = binary_ne_grid(fpuzz_grid)
    n = fpuzz_grid[0][0]
    
    for cage in fpuzz_grid[1:]:
        if len(cage) == 2:
            cell = vars[cage[0]%10-1][cage[0]//10-1]
            target = cage[1]
            
            c = Constraint('Cell-{}'.format(cage[0]), cell)
            c.add_satisfying_tuples((target))
            csp.add_constraint(c)
        
        else:
            operation = cage.pop(-1)
            target = cage.pop(-1)
            cells = [vars[i%10-1][i//10-1] for i in cage]
            
            c = Constraint('Cage-'+'-'.join([str(v) for v in cage]), cells)
            
            # disallow duplicates if all cells in same row OR same column
            if len(set([x//10 for x in cage])) == 1 or len(set([x%10-1 for x in cage])) == 1:
                combinations = list(itertools.combinations(range(1,n+1), len(cage)))
            else:
                combinations = list(itertools.combinations_with_replacement(range(1,n+1), len(cage)))
                
            # combinations = list(itertools.combinations_with_replacement(range(1,n+1), len(cage)))    
            satisfying = []
            
            for combo in combinations:
            
                if operation == 0:
                    # add
                    if sum(combo) == target:
                        satisfying += list(itertools.permutations(combo))
                elif operation == 1:
                    # subtract
                    permutations = list(itertools.permutations(combo))
                    for perm in permutations:
                        perm = list(perm)
                        diff = perm.pop(0)
                        for v in perm:
                            diff -= v
                        if diff == target:
                            satisfying += list(itertools.permutations(combo))
                            break
                elif operation == 2:
                    # divide
                    permutations = list(itertools.permutations(combo))
                    for perm in permutations:
                        perm = list(perm)
                        quotient = perm.pop(0)
                        for v in perm:
                            quotient /= v
                        if quotient == target:
                            satisfying += list(itertools.permutations(combo))
                            break
                elif operation == 3:
                    # multiply
                    prod = 1
                    for v in combo:
                        prod*=v
                    if prod == target:
                        satisfying += list(itertools.permutations(combo))
                
            c.add_satisfying_tuples(satisfying)
            csp.add_constraint(c)
    
    return csp, vars

# for c in csp.vars_to_cons[csp.vars[-1]]:
#     print(c.name)
#     print(c.scope)
#     print(c.sat_tuples)
#     print("***\n")