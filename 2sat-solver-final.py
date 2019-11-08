#!/usr/bin/env python
# coding: utf-8

# In[48]:


import math
import random
import gc
import sys
import threading
from io import StringIO
from time import time
from tqdm import tqdm

## Making the implication graph
def make_sat_graph(clauses):
    n = len(clauses)
    def var_index(var):
        if var < 0: return n - var
        else: return var
    res = ''
    for clause in clauses:
        res += '%i %i\n' % (var_index(-clause[0]), var_index(clause[1]))
        res += '%i %i\n' % (var_index(-clause[1]), var_index(clause[0]))
    #print(res)
    return res


################################################################################
#######      Kosaraju's SSC algorithm implementation from part 1          ######
################################################################################

def readDirectedGraph(str):
    f = StringIO(str)

    adjlist = []
    adjlist_reversed = []

    line = f.readline()
    while line != '':
        num1, num2 = line.split()
        v_from = int(num1)
        v_to = int(num2)
        max_v = max(v_from, v_to)

        while len(adjlist) < max_v:
            adjlist.append([])
        while len(adjlist_reversed) < max_v:
            adjlist_reversed.append([])

        adjlist[v_from-1].append(v_to-1)
        adjlist_reversed[v_to-1].append(v_from-1)

        line = f.readline()

    #print(adjlist)
    return adjlist, adjlist_reversed


t = 0
s = None
n = 0
explored = None
leader = None
current_ssc = None
contradictory_ssc = None
sorted_by_finish_time = None

def DFS_Loop_1(graph_rev, n):

    global t, explored, sorted_by_finish_time
    t = 0
    explored = [False]*n
    sorted_by_finish_time = [None]*n

    for i in reversed(range(n)):
        if not explored[i]:
            DFS_1(graph_rev, i)


def DFS_1(graph_rev, i):

    global t, explored

    explored[i] = True

    for v in graph_rev[i]:
        if not explored[v]:
            DFS_1(graph_rev, v)

    sorted_by_finish_time[t] = i
    t += 1


def DFS_Loop_2(graph):

    global current_ssc, explored, contradictory_ssc, sorted_by_finish_time

    explored = [False]*len(graph)

    for i in reversed(range(len(graph))):
        if not explored[sorted_by_finish_time[i]]:
            scc_size = 0
            # Here we collect all the members
            # of the next SCC using DFS.
            current_ssc = set()
            contradictory_ssc = False
            DFS_2(graph, sorted_by_finish_time[i])
            if contradictory_ssc: break
    #print("current_ssc",current_ssc)
    #print("sorted by finish time:",sorted_by_finish_time)
    return contradictory_ssc


def DFS_2(graph, i):

    global explored, current_ssc, contradictory_ssc

    explored[i] = True
    current_ssc.add(i)

    # Check for unsatisfabilty indicator
    if i < n:
        if (i+n) in current_ssc:
            contradictory_ssc = True
    elif (i-n) in current_ssc:
        contradictory_ssc = True

    for v in graph[i]:
        if not explored[v]:
            DFS_2(graph, v)


def kosaraju_contradictory_ssc(graph, graph_rev):
    #print("this is the graph",graph)
    DFS_Loop_1(graph_rev, len(graph))
    contradictory_ssc = DFS_Loop_2(graph)

    return contradictory_ssc

def dfs(filename):
    f = open(filename)
    formula = []
    for line in f:
        if line[0] == "c":
            pass
        elif line[0] == "p":
            x = line.split()
            #numlit = x[2]
            #clauselit = x[3]
        else:
            templit = []
            for x in line.split():
                if int(x) != 0:
                    templit.append(int(x))
            formula.append(templit)
    sat_graph = make_sat_graph(formula)
    graph, graph_rev = readDirectedGraph(sat_graph)
    start = time()
    contradictory_ssc = kosaraju_contradictory_ssc(graph, graph_rev)
    print(sorted_by_finish_time) 
    print(explored)
    res = 'FORMULA UNSATISFIABLE' if contradictory_ssc else 'FORMULA SATISFIABLE'
    print(res)
    time_taken = time() - start

    return time_taken


# In[64]:


import random
import math

def random_solve(file):

    # Reading inputs from the input file and storing clauses in a list
    file = open(file, "r")
    #noOfClauses = int( file.readline() )

    clauses = []
    for line in file:
        if line[0] == "c":
            pass
        elif line[0] == "p":
            x = line.split()
            numlit = int(x[2])
            noOfClauses = int(x[3])
        else:
            clauseLiteralsInfo=line.split()
            clause = Clause( firstLiteral = int(clauseLiteralsInfo[0]), secondLiteral = int(clauseLiteralsInfo[1]))
            clauses.append(clause)
    # print(noOfClauses)

    start = time()

    # Calling papadimitriou's algorithm
    papadimitriou(clauses, noOfClauses,numlit)
    return time() - start

def papadimitriou(clauses, noOfClauses,numlit):
    """Funtion to compute where or not a instance satisfies the 2-SAT property.
       Inputs are the clauses and number of clauses."""
    # List to store the values of the literals initialized above
    answers = []
    answers.append( "NaN" )
    for x in range(1, noOfClauses+1):
        x = random.random()
        if x > 0.5:
            answers.append(True)
        else:
            answers.append(False)

    # Algorithm to run 2 * n^2 * logn times (loops)
    twoNSquared = 2 * (noOfClauses ** 2)

    # Flag to keep track if the input satisfies 2-SAT propety or not
    isSatisfying = False

    # Running for loop of algorithm
    for k in range( int( math.log(noOfClauses, 2) ) ):

#         print("ON LOOP NUMBER :" + str(k))

        for j in range(twoNSquared):

            # Flag to keep track if all the clauses are satisfied or not
            # Helps in breaking early
            areAllClausesSatisfied = True

            # Variable to keep track of number of clauses satisfied till now
            # (of the clauses scanned)
            noOfSatisfyingClauses = 0

            # Running loop for every clause
            for clause in clauses:

                # If clause is not satisfying itself individually
                if clause.isSatisfyingCriteria(answers) == False:
                    areAllClausesSatisfied = False

                    # Randomly choosing a literal and negating its value
                    randomlyChosenLiteral = random.choices([clause.firstLiteral,clause.secondLiteral])[0]
                    answers[ abs(randomlyChosenLiteral) ] = not( answers[ abs(randomlyChosenLiteral) ] )

                    break

                # Else if the clause is satisfying itself individually
                else:
                    noOfSatisfyingClauses += 1

#             print("The number of clauses satisfying criteria till now (of the ones which have been checked in a linear pass) is :" + str(noOfSatisfyingClauses) )

            # Breaking early if all the clauses are satisfied
            if areAllClausesSatisfied == True:
                isSatisfying = True
                break

        #Printing answers, values of the literals if 2-SAT property is satisfied by clauses
        if isSatisfying == True:
            #Printing results
            print("The answers of the literals respectively are as follows :- \n\n")
            for i in range(1, numlit+1):
                print("Literal " + str(i) + " : " + str(answers[i]) )
            print("FORMULA SATISFIABLE")
            break

    #Printing not satisfiable if none of the iterations are able to find any solution
    if isSatisfying == False:
        print("FORULA UNSATISFIABLE")

class Clause:

    def __init__(self, firstLiteral, secondLiteral):
        """Function to initialize a new clause."""

        self.firstLiteral = firstLiteral
        self.secondLiteral = secondLiteral

    def __str__(self):
        """Function to print the clause in the required way."""

        return str(self.firstLiteral) + " OR " + str(self.secondLiteral)

    def isSatisfyingCriteria(self, answers):
        """Function to check whether the clause is satisfied or not."""

        # Negative value means negation
        # Positive value means no negation

        if self.firstLiteral < 0:
            boolean1 = not( answers[ abs(self.firstLiteral) ] )
        else:
            boolean1 = answers[ self.firstLiteral ]

        if self.secondLiteral < 0:
            boolean2 = not( answers[ abs(self.secondLiteral) ] )
        else:
            boolean2 = answers[ self.secondLiteral ]

        # Returning OR result of both the literals
        return boolean1 or boolean2


# In[50]:


# parse formula

# random_solve('2sat1.txt')
# f = open('2sat1.txt')
# clau = []
# for line in f:
#     if line[0] == "c":
#         pass
#     elif line[0] == "p":
#         x = line.split()
#         numlit = x[2]
#         clauselit = x[3]
#     else:
#         templit = []
#         for x in line.split():
#             if int(x) != 0:
#                 templit.append(int(x))
#         clau.append(templit)
# print(clau)

dfs('2sat1.txt')

# g = open('2sat.txt')
# #n= int(f.readline())
# formula = [[int(x) for x in line.split()] for line in g]
# print(formula)
# dfs(formula)

# %%
