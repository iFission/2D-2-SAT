#!/usr/bin/env python

import math
import random
import sys
from io import StringIO
from time import time
from tqdm import tqdm


def make_sat_graph(clauses):
    n = len(clauses)

    def var_index(var):
        if var < 0: return n - var
        else: return var

    res = ''
    for clause in clauses:
        res += '%i %i\n' % (var_index(-clause[0]), var_index(clause[1]))
        res += '%i %i\n' % (var_index(-clause[1]), var_index(clause[0]))
    return res


def read_directed_graph(str):
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

        adjlist[v_from - 1].append(v_to - 1)
        adjlist_reversed[v_to - 1].append(v_from - 1)

        line = f.readline()

    return adjlist, adjlist_reversed


t = 0
s = None
n = 0
explored = None
leader = None
current_ssc = None
contradictory_ssc = None
sorted_by_finish_time = None


def dfs_loop_1(graph_rev, n):

    global t, explored, sorted_by_finish_time
    t = 0
    explored = [False] * n
    sorted_by_finish_time = [None] * n

    for i in reversed(range(n)):
        if not explored[i]:
            dfs_1(graph_rev, i)


def dfs_1(graph_rev, i):

    global t, explored

    explored[i] = True

    for v in graph_rev[i]:
        if not explored[v]:
            dfs_1(graph_rev, v)

    sorted_by_finish_time[t] = i
    t += 1


def dfs_loop_2(graph):

    global current_ssc, explored, contradictory_ssc, sorted_by_finish_time

    explored = [False] * len(graph)

    for i in reversed(range(len(graph))):
        if not explored[sorted_by_finish_time[i]]:
            scc_size = 0
            current_ssc = set()
            contradictory_ssc = False
            dfs_2(graph, sorted_by_finish_time[i])
            if contradictory_ssc: break
    return contradictory_ssc


def dfs_2(graph, i):

    global explored, current_ssc, contradictory_ssc

    explored[i] = True
    current_ssc.add(i)

    # Check for unsatisfabilty indicator
    if i < n:
        if (i + n) in current_ssc:
            contradictory_ssc = True
    elif (i - n) in current_ssc:
        contradictory_ssc = True

    for v in graph[i]:
        if not explored[v]:
            dfs_2(graph, v)


def kosaraju_contradictory_ssc(graph, graph_rev):
    #print("this is the graph",graph)
    dfs_loop_1(graph_rev, len(graph))
    contradictory_ssc = dfs_loop_2(graph)

    return contradictory_ssc


def dfs(filename):
    f = open(filename, "r")

    f = open(filename)
    formula = []
    for line in f:
        if line[0] == "c":
            pass
        elif line[0] == "p":
            x = line.split()
        else:
            templit = []
            for x in line.split():
                if int(x) != 0:
                    templit.append(int(x))
            formula.append(templit)

    sat_graph = make_sat_graph(formula)
    graph, graph_rev = read_directed_graph(sat_graph)
    contradictory_ssc = kosaraju_contradictory_ssc(graph, graph_rev)
    solution = 'FORMULA UNSATISFIABLE' if contradictory_ssc else 'FORMULA SATISFIABLE'
    return solution


import random
import math


def random_solve(file):

    file = open(file, "r")

    clauses_random = []
    for line in file:
        if line[0] == "c":
            pass
        elif line[0] == "p":
            x = line.split()
            numlit = int(x[2])
            no_clauses = int(x[3])
        else:
            clauseLiteralsInfo = line.split()
            clause = Clause(literal_1=int(clauseLiteralsInfo[0]),
                            literal_2=int(clauseLiteralsInfo[1]))
            clauses_random.append(clause)
    papadimitriou(clauses_random, no_clauses, numlit)


def papadimitriou(clauses, no_clauses, numlit):
    """Funtion to compute where or not a instance satisfies the 2-SAT property.
       Inputs are the clauses and number of clauses."""
    answers = []
    answers.append("NaN")
    for x in range(1, no_clauses + 1):
        x = random.random()
        if x > 0.5:
            answers.append(True)
        else:
            answers.append(False)

    is_satisfying = False

    for k in range(int(math.log(no_clauses, 2))):
        for j in range(2 * (no_clauses**2)):

            all_claused_satisfied = True

            no_satisfying_clauses = 0

            for clause in clauses:

                if clause.is_satisfying(answers) == False:
                    all_claused_satisfied = False

                    randomlyChosenLiteral = random.choices(
                        [clause.literal_1, clause.literal_2])[0]
                    answers[abs(randomlyChosenLiteral)] = not (
                        answers[abs(randomlyChosenLiteral)])

                    break

                else:
                    no_satisfying_clauses += 1

            if all_claused_satisfied == True:
                is_satisfying = True
                break

        if is_satisfying == True:
            print("FORMULA SATISFIABLE")
            outstr = ""
            for i in range(1, numlit + 1):
                if answers[i] == False:
                    outstr += "0 "
                else:
                    outstr += "1 "
            print(outstr)
            break

    if is_satisfying == False:
        print("FORULA UNSATISFIABLE")


class Clause:
    def __init__(self, literal_1, literal_2):
        self.literal_1 = literal_1
        self.literal_2 = literal_2

    def __str__(self):
        return str(self.literal_1) + " OR " + str(self.literal_2)

    def is_satisfying(self, answers):
        if self.literal_1 < 0:
            boolean_1 = not (answers[abs(self.literal_1)])
        else:
            boolean_1 = answers[self.literal_1]

        if self.literal_2 < 0:
            boolean_2 = not (answers[abs(self.literal_2)])
        else:
            boolean_2 = answers[self.literal_2]

        return boolean_1 or boolean_2


if __name__ == "__main__":
    # Input CNF filename from terminal argument
    try:
        filename = sys.argv[1]
        dfs(filename)
        random_solve(filename)
    except IndexError as e:
        print("no cnf file specified")
        print("Input cnf file as the second argument")
        print("example:")
        print("python3 2sat-solver.py 2sat.txt")
