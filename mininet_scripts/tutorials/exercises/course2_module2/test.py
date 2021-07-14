from pulp import LpMinimize, LpMaximize, LpProblem, LpStatus, lpSum, LpVariable, LpAffineExpression, constants

1*max_util + 0
SUBJECT TO
_C1: ('h1',_'h2')_on_(h1,_s1) + ('h1',_'h2')_on_(h2,_s1)
 - ('h1',_'h2')_on_(s1,_h1) - ('h1',_'h2')_on_(s1,_h2) = 0

_C2: ('h1',_'h2')_on_(h1,_s1) - ('h1',_'h2')_on_(s1,_h1) = 2

_C3: - ('h1',_'h2')_on_(h1,_s1) + ('h1',_'h2')_on_(s1,_h1) = 2

VARIABLES
0 <= ('h1',_'h2')_on_(h1,_s1) <= 2 Integer
0 <= ('h1',_'h2')_on_(h2,_s1) <= 2 Integer
0 <= ('h1',_'h2')_on_(s1,_h1) <= 2 Integer
0 <= ('h1',_'h2')_on_(s1,_h2) <= 2 Integer
0 <= max_util Integer

model = LpProblem(name="small-problem", sense=LpMinimize)

# Initialize the decision variables
x = LpVariable(name="a", lowBound=0, upBound=2)
y = LpVariable(name="b", lowBound=0, upBound = 2)
y = LpVariable(name="c", lowBound=0, upBound = 2)
y = LpVariable(name="d", lowBound=0, upBound = 2)
y = LpVariable(name="m", lowBound=0, upBound = 2)

# Add the constraints to the model
model += (a + b - c - d == 0, "c1")
model += (a - c == 2, "c2")
model += (, "yellow_constraint")
model += (-x + 5 * y == 15, "green_constraint")

# Add the objective function to the model
obj_func = x + 2 * y
model += obj_func

# Solve the problem
status = model.solve()

print(f"status: {model.status}, {LpStatus[model.status]}")
