'''
Calendar Satisfaction Problem (CSP) Solver
Designed to make scheduling those meetings a breeze! Suite of tools
for efficiently scheduling some n meetings in a given datetime range
that abides by some number of constraints.

In this module:
- A solver that uses the backtracking exact solver approach
- Tools for pruning domains using node and arc consistency
'''
from datetime import *
from date_constraints import *
from dataclasses import *
from copy import *


# CSP Backtracking Solver
# ---------------------------------------------------------------------------
def solve(n_meetings: int, date_range: list[set[datetime]] | set[datetime], constraints: set[DateConstraint]) -> Optional[list[datetime]]:
    '''
    When possible, returns a solution to the given CSP based on the need to
    schedule n meetings within the given date range and abiding by the given
    set of DateConstraints.
      - Implemented using the Backtracking exact solution method
      - May return None when the CSP is unsatisfiable
    
    Parameters:
        n_meetings (int):
            The number of meetings that must be scheduled, indexed from 0 to n-1
        date_range (list[set[datetime]] | set[datetime]):
            The range of datetimes in which the n meetings must be scheduled; by default,
            these are each separated a day apart, but there's nothing to stop these from
            being meetings scheduled down to the second
            [!] WARNING: AVOID ALIASING -- Remember that each variable must have its
            own domain but what's provided is a single reference to a set of datetimes
        constraints (set[DateConstraint]):
            A set of DateConstraints specifying how the meetings must be scheduled.
            See DateConstraint documentation for different types of DateConstraints
            that might be found, and useful methods for implementing this solver.
    
    Returns:
        Optional[list[datetime]]:
            If a solution to the CSP exists:
                Returns a list of datetimes, one for each of the n_meetings, where the
                datetime at each index corresponds to the meeting of that same index
            If no solution is possible:
                Returns None
    '''
    
    def csp_backtracker(vars: int, doms: Any, date_constraints: set[DateConstraint]) -> Optional[list[datetime]]:
        '''
        A helper function that applies the backtracking algorithm to find a solution
        for the CSP problem, considering domain and constraint consistency.

        Parameters:
            vars (int): The number of variables (meetings) to be scheduled.
            doms (list[set[datetime]]): A list of domains for each variable (the available datetimes for each meeting).
            date_constraints (set[DateConstraint]): A set of DateConstraints that must be satisfied for the solution.

        Returns:
            Optional[list[datetime]]:
                If a solution is found, returns a list of datetime values assigned to each variable (meeting).
                If no solution is found, returns None.
        '''
        
        # Convert doms to work with node and arc consistency, does not work otherwise
        doms = [date_range for _ in range(n_meetings)]
        node_consistency(doms, date_constraints)
        arc_consistency(doms, date_constraints)
        assignments = [None] * vars
        return recursive_csp_backtracker(assignments, vars, doms, date_constraints)

    def recursive_csp_backtracker(assignments: List[Any], vars: int, doms: list[set[datetime]], constraints: set[DateConstraint]) -> Optional[list[datetime]]:
        '''
        The recursive backtracking function that explores all possible assignments for the variables,
        checking each one against the constraints until a valid solution is found or all possibilities are exhausted.

        Parameters:
            assignments (List[Any]): A list of current assignments for each variable (meeting).
            vars (int): The number of variables (meetings).
            doms (list[set[datetime]]): The domains for each variable (the available datetimes for each meeting).
            constraints (set[DateConstraint]): A set of DateConstraints that must be satisfied for the solution.

        Returns:
            Optional[list[datetime]]:
                If a valid assignment is found, returns a list of datetime values assigned to each variable (meeting).
                If no solution is found, returns None.
        '''
        
        # Loop until all assignments are complete or no solution found
        for assignment in assignments:
            if assignment:
                continue
            else:
                current_var = assignments.index(assignment)
                for dom in doms[current_var]:
                    assignments[current_var] = dom
                    satisfied = True
                    for constraint in constraints: # Loops until all constraints are satisfied
                        if not constraint.is_satisfied_by_assignment(assignments):
                            satisfied = False
                            assignments[current_var] = None
                            break
                    if satisfied:
                        result = recursive_csp_backtracker(assignments, vars, doms, constraints)
                        if result:
                            return result
                    assignments[current_var] = None
                return None
        return assignments
     

    return csp_backtracker(n_meetings, date_range, constraints)

# CSP Filtering: Node Consistency
# ---------------------------------------------------------------------------
def node_consistency(domains: list[set[datetime]], constraints: set[DateConstraint]) -> None:
    '''
    Enforces node consistency for all variables' domains given in the set of domains.
    Meetings' domains' index in each of the provided constraints correspond to their index
    in the list of domains.
    
    [!] Note: Only applies to Unary DateConstraints, i.e., those whose arity() method
    returns 1
    
    Parameters:
        domains (list[set[datetime]]):
            A list of domains where each domain is a set of possible date times to assign
            to each meeting. Each domain in the given list is indexed such that its index
            corresponds to the indexes of meetings mentioned in the given constraints.
        constraints (set[DateConstraint]):
            A set of DateConstraints specifying how the meetings must be scheduled.
            See DateConstraint documentation for different types of DateConstraints
            that might be found, and useful methods for implementing this solver.
            [!] Hint: see a DateConstraint's is_satisfied_by_values
    
    Side Effects:
        Although no values are returned, the values in any pruned domains are changed
        directly within the provided domains parameter
    ''' 
    
    # Create copy to prevent error of set size changing during iteration
    dom_copy: list[set[datetime]] = [set(dom) for dom in domains]

    for current_index, dom in enumerate(domains):
        current_dom = dom_copy[current_index]
        for date in dom:
            for constraint in constraints:
                if constraint.arity() == 1 and constraint.L_VAL == current_index: # Check for unary constraints
                    if not constraint.is_satisfied_by_values(date):
                        current_dom.remove(date)
                else: 
                    continue
        domains[current_index] = current_dom



# CSP Filtering: Arc Consistency
# ---------------------------------------------------------------------------
class Arc:
    '''
    Helper Arc class to be used to organize domains for pruning during the AC-3
    algorithm, organized as (TAIL -> HEAD) Arcs that correspond to a given
    CONSTRAINT.
    
    [!] Although you do not need to, you *may* modify this class however you see
    fit to accomplish the arc_consistency method
    
    Attributes:
        CONSTRAINT (DateConstraint):
            The DateConstraint represented by this arc
        TAIL (int):
            The index of the meeting variable at this arc's tail.
        HEAD (int):
            The index of the meeting variable at this arc's head.
    
    [!] IMPORTANT: By definition, the TAIL = CONSTRAINT.L_VAL and
        HEAD = CONSTRAINT.R_VAL
    '''
    
    def __init__(self, constraint: DateConstraint):
        '''
        Constructs a new Arc from the given DateConstraint, setting this Arc's
        TAIL to the constraint's L_VAL and its HEAD to the constraint's R_VAL
        
        Parameters:
            constraint (DateConstraint):
                The constraint represented by this Arc
        '''
        self.CONSTRAINT: DateConstraint = constraint
        self.TAIL: int = constraint.L_VAL
        if isinstance(constraint.R_VAL, int):
            self.HEAD: int = constraint.R_VAL
        else:
            raise ValueError("[X] Cannot create Arc from Unary Constraint")
    
    def __eq__(self, other: Any) -> bool:
        if other is None: return False
        if not isinstance(other, Arc): return False
        return self.CONSTRAINT == other.CONSTRAINT and self.TAIL == other.TAIL and self.HEAD == other.HEAD
    
    def __hash__(self) -> int:
        return hash((self.CONSTRAINT, self.TAIL, self.HEAD))
    
    def __str__(self) -> str:
        return "Arc[" + str(self.CONSTRAINT) + ", (" + str(self.TAIL) + " -> " + str(self.HEAD) + ")]"
    
    def __repr__(self) -> str:
        return self.__str__()

def arc_consistency(domains: list[set[datetime]], constraints: set[DateConstraint]) -> None:
    '''
    Enforces arc consistency for all variables' domains given in the set of domains.
    Meetings' domains' index in each of the provided constraints correspond to their index
    in the list of domains.
    
    [!] Note: Only applies to Binary DateConstraints, i.e., those whose arity() method
    returns 2
    
    Parameters:
        domains (list[set[datetime]]):
            A list of domains where each domain is a set of possible date times to assign
            to each meeting. Each domain in the given list is indexed such that its index
            corresponds to the indexes of meetings mentioned in the given constraints.
        constraints (set[DateConstraint]):
            A set of DateConstraints specifying how the meetings must be scheduled.
            See DateConstraint documentation for different types of DateConstraints
            that might be found, and useful methods for implementing this solver.
            [!] Hint: see a DateConstraint's is_satisfied_by_values
    
    Side Effects:
        Although no values are returned, the values in any pruned domains are changed
        directly within the provided domains parameter
    '''
    
    def ac_preprocessing(doms: list[set[datetime]], constraints: set[DateConstraint]) -> None:
        '''
        Processes the given constraints to identify binary constraints (arity of 2) and
        initializes the set of arcs. The function adds arcs to a set, then processes each
        arc, removing inconsistent values from the domains of the variables involved.

        Parameters:
            doms (list[set[datetime]]): The list of domains for each variable (meeting).
            constraints (set[DateConstraint]): The set of constraints specifying the relationships
                                               between meetings.
        
        '''
        
        arcs = set()
        
        # Initialize arcs
        for constraint in constraints:
            if constraint.arity() > 1:
                arcs.add(Arc(constraint))
                arcs.add(Arc(constraint.get_reverse()))
        
        # Loops until arc set is empty        
        while arcs:
            current_arc = arcs.pop() 
            if inconsistent_val_removal(domains, current_arc):
                for constraint in constraints:
                    if constraint.arity() > 1 and constraint.R_VAL == current_arc.TAIL: # Check for binary constraints
                        arcs.add(Arc(constraint))         
            
    def inconsistent_val_removal(doms: list[set[datetime]], current_arc: Arc) -> bool:
        '''
        Removes values from the tail's domain if no consistent value in the head's domain satisfies
        the constraint for the given arc. If any value is removed from the tail's domain, the function
        returns True, indicating a change in the domains.

        Parameters:
            doms (list[set[datetime]]): The list of domains for each variable (meeting).
            current_arc (Arc): The arc representing the constraint between two variables.

        Returns:
            bool: True if any value was removed from the tail's domain, False otherwise.
        '''
        removed = False
        tail_dom = doms[current_arc.TAIL]
        head_dom = doms[current_arc.HEAD]
        
        # Create copy to prevent error of set size changing during iteration
        tail_dom_copy = tail_dom.copy()
        for tail in tail_dom_copy:
            inconsistent = True
            for head in head_dom:
                if current_arc.CONSTRAINT.is_satisfied_by_values(tail, head):
                    inconsistent = False
                    break
            if inconsistent:
                tail_dom.remove(tail)
                removed = True

        return removed
    
    ac_preprocessing(domains, constraints)
        
