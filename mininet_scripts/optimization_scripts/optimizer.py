from pulp import LpMinimize, LpMaximize, LpProblem, LpStatus, lpSum, LpVariable, LpAffineExpression, constants
from enum import Enum
import operator

class ObjectiveType(Enum):
    MIN = 0
    MAX = 1

class Optimizer:

    def __init__(self, obj_type):
        self.model = LpProblem(name="routing", 
                               sense=(LpMinimize if obj_type == ObjectiveType.MIN 
                                                 else LpMaximize))
        self.valid_ops = ['<', '<=', '>', '>=', '=='] 
        self.vars = {}
        self.constrs = {}
        self.obj = None

    def add_boolean_var(self, name):
        if name in self.vars:
            print(f"{name} is already defined")
            return

        self.vars[name] = LpVariable(name, cat="Binary")

    def add_integer_var(self, name, lower_bound=None, upper_bound=None):
        if name in self.vars:
            print(f"{name} is already defined")
            return

        self.vars[name] = LpVariable(name, lowBound=lower_bound, 
                                     upBound=upper_bound, cat="Integer")

    '''
    def add_continuous_var(self, name, lower_bound=None, upper_bound=None):
        if name in self.vars:
            print(f"{name} is already defined")
            return

        self.vars[name] = LpVariable(name, lowBound=lower_bound, 
                                     upBound=upper_bound, cat="Continuous")
    '''

    def add_constraint(self, name, rhs, op, lhs):
        if name in self.constrs:
            print(f"{name} is already defined")
            return

        if not op in self.valid_ops:
            print(f"Invalid operator {op}, {op} is not one of {self.valid_ops}")
            return
        
        rhs = lpSum(rhs)
        lhs = lpSum(lhs)
        constr = None
        if op == "<":
            constr = rhs < lhs
        elif op == "<=":
            constr = rhs <= lhs
        elif op == ">":
            constr = rhs > lhs
        elif op == ">=":
            constr = rhs >= lhs
        elif op == "==":
            constr = rhs == lhs

        if constr is None:
            print("Should not reach here")
            return

        self.constrs[name] = constr
        self.model += constr

    def add_objective_function(self, expr):
        if (not isinstance(expr, LpAffineExpression) and
           not isinstance(expr, LpVariable)):
            print(f"{expr} is not a valid expression")
            return

        if not self.obj is None:
            print(f"There is already an objective {self.obj}")
            return

        self.obj = expr
        self.model += expr

    def solve(self):
        self.model.solve()
        print(self.model.status)
        if self.model.status != constants.LpStatusOptimal:
            print("Could not solve LP")
            return None

        print("Solved!")

        var_assignments = {}
        for var in self.model.variables():
            var_assignments[var.name] = var.value()

        return var_assignments


