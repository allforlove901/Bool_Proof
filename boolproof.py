# Name:         Brett Nelson
# Course:       CSC 480
# Instructor:   Daniel Kauffman
# Assignment:   Bool Proof I
# Term:         Winter 2019

import queue
import math
import itertools

# function to get variables to be used for constraint propagation along with
#   their respective domains
# board - a Tuple of tuples of ints representing a board
def get_vars(board):
    vars = {}
    for i in range(len(board)):
        for j in range(len(board[i])):
            var = board[i][j]
            if var != None:
                index = i * len(board[i]) + j
                add = get_combinations(board, var, i, j)
                vars[index] = add
    return vars


# function to get a list of all arcs, pairs of variables sharing a
#   binary constraint
# board - a Tuple of tuples of ints representing a board
def get_arcs(board):
    pairs = []
    # get vars
    vars = get_vars(board)
    # create a list of keys
    var_indices = []
    for key in vars:
        var_indices.append(key)

    # loop over all clues
    for i in range(len(var_indices)):
        clue_index = var_indices[i]
        # get list of adjacent unknowns
        combination = vars[clue_index][0]
        # loop over preceding clues for common constraints
        for k in range(i + 1, len(var_indices)):
            other_clue_index = var_indices[k]
            # loop over all adjacent unknowns
            for key in combination:
                if key in vars[other_clue_index][0]:
                    # common constraint found, add to pairs
                    ind1 = var_indices[i]
                    ind2 = var_indices[k]
                    if ind1 < ind2:
                        pairs.append((ind1, ind2))
                    else:
                        pairs.append((ind2, ind1))
                    break
    pairs = sort_pairs(pairs)
    return set(pairs)


# function to get all possible borad arrangements with mines
# board - a Tuple of tuples of ints representing a board
# vars - a dictionary of variable values
def check_models(board, vars = None, arcs = None):
    vars = get_vars(board)
    mine_spots = get_possible_mine_spots(board)
    sets = queue.Queue()
    sets.put({})
    level = 0
    # while level is less than number of mines possible, create new sets and
    # test to see if they pass constraints
    while level < len(mine_spots):
        level_set_len = sets.qsize()
        for i in range(level_set_len):
            next_set = sets.get()
            add_true = next_set.copy()
            add_false = next_set.copy()
            add_true[mine_spots[level]] = True
            add_false[mine_spots[level]] = False
            if check_constraint(add_true, vars):
                sets.put(add_true)
            if check_constraint(add_false, vars):
                sets.put(add_false)
        level += 1
    return dicts_to_set(board, sets)


# function to guess model
# vars - a dictionary of variable values
def guess_model(models, vars = None, arcs = None):
    best_model = None
    num_rows = num_cols = None
    num_models = len(models)
    # get dimensions
    for m in models:
        num_rows = len(m)
        num_cols = len(m[0])
        break
    mine_freqs = get_mine_freqs(models, num_rows, num_cols)

    # loop through models, scoring each one
    # if a model has better score than max, replace model and update max score
    max_score = -1
    for model in models:
        score = 1
        for i in range(num_rows):
            for j in range(num_cols):
                # mine at spot, multiply score by P
                if model[i][j] != None and model[i][j] < 0:
                    # mine at spot, multiply score by P
                    score *= mine_freqs[i][j]
                else:
                    # mine at spot, multiply score by P
                    score *= (1 - mine_freqs[i][j])
        if score > max_score:
            best_model = model
            max_score = score
    return best_model


# function to get mine frequency values for each space
def get_mine_freqs(models, num_rows, num_cols):
    # get each space's mine probability or P
    # create array of possble mine spots
    mine_freqs = [[0] * num_cols for i in range(num_rows)]
    # for each model, check if mine exists at that space
    for model in models:
        for i in range(len(model)):
            for j in range(len(model[i])):
                if model[i][j] != None and model[i][j] < 0:
                    mine_freqs[i][j] += 1
    for i in range(len(mine_freqs)):
        mine_freqs[i] = [x / len(models) for x in mine_freqs[i]]
    return mine_freqs


# function to get a set of boards from a list of sets
def dicts_to_set(board, sets):
    boards = []
    num_sets = sets.qsize()
    board_len = len(board)
    row_len = len(board[0])
    # for each set, create a board
    for k in range(num_sets):
        s = sets.get()
        new_board = []
        # for each row index, create a row of values
        for i in range(board_len):
            row = []
            # for each column add a mine, clue, or None
            for j in range(row_len):
                if board[i][j] == None: # no clue found, check if mine
                    index = i * row_len + j
                    if index in s and s[index]: # mine found, add it
                        row.append(-1)
                    else: # no mine, add a None instead
                        row.append(None)
                else: # clue found, add it
                    row.append(board[i][j])
            new_board.append(tuple(row))
        boards.append(tuple(new_board))
    return set(boards)


# function to get all possible mine spots
def get_possible_mine_spots(board):
    possible = []
    clues = get_clues(board)
    # for each clue, get surrounding spots and track if not already tracked
    for clue in clues:
        row = clue // len(board[0])
        col = clue % len(board[0])
        adj_uns = get_adj_unknowns(board, row, col)[0]
        for i in adj_uns:
            if i not in possible:
                possible.append(i)
    return possible


# function to check if a constraint is okay with vars
def check_constraint(constraint, vars):
    # loop through every var, checking to make sure they allow constraint
    for var in vars:
        combinations = vars[var]
        var_pass = False
        # loop through each combination, if one passes, then the var passes
        for comb in combinations:
            comb_pass = True
            # loop through constraint list to look for conflicts,
            # if one conflict exists, combination does not pass
            # only consider constraints that are in domain of this var
            for c in constraint:
                if c in comb and comb[c] != constraint[c]:
                    comb_pass = False
                    break
            if comb_pass:
                var_pass = True
                break
        # if one var fails, constraint doesn't pass
        if not var_pass:
            return False
    return True


# helper function to get all combinations of mine setups at a spot
def get_combinations(board, var, row, col):
    combinations = []
    # get adjacent unknowns
    get_adj_unknowns_res = get_adj_unknowns(board, row, col)
    adj_unknowns = get_adj_unknowns_res[0]
    visible_adj_mines = get_adj_unknowns_res[1]
    # get combinations using unfound mines left
    combs = itertools.combinations(adj_unknowns, var - len(visible_adj_mines))
    # generate a combination mapping for each combination
    for c in combs:
        combination = {}
        for i in adj_unknowns:
            if i in c:
                combination[i] = True
            else:
                combination[i] = False
        for mine in visible_adj_mines:
            combination[mine] = True
        combinations.append(combination)
    return combinations


# function to get unkown adjacent spots
def get_adj_unknowns(board, row, col):
    adj_unknowns = []
    mines = []
    # get board dimensions
    n_rows = len(board)
    n_cols = len(board[0])
    # get restrictions
    first_row = (row == 0)
    last_row = (row == n_rows - 1)
    first_col = (col == 0)
    last_col = (col == n_cols - 1)

    # go through every possible spot and check if none
    if not (first_row or first_col):
        if board[row - 1][col - 1] == None:
            adj_unknowns.append((row - 1) * n_cols + col - 1)
        elif board[row - 1][col - 1] < 0:
            mines.append((row - 1) * n_cols + col - 1)
    if not first_row:
        if board[row - 1][col] == None:
            adj_unknowns.append((row - 1) * n_cols + col)
        elif board[row - 1][col] < 0:
            mines.append((row - 1) * n_cols + col)
    if not (first_row or last_col):
        if board[row - 1][col + 1] == None:
            adj_unknowns.append((row - 1) * n_cols + col + 1)
        elif board[row - 1][col + 1] < 0:
            mines.append((row - 1) * n_cols + col + 1)

    return extend_get_au(board, row, col, adj_unknowns, mines, first_row,
        last_row, first_col, last_col, n_rows, n_cols)


# extension method to get around line count issue
def extend_get_au(board, row, col, adj_unknowns, mines, first_row, last_row,
        first_col, last_col, n_rows, n_cols):
    if not first_col:
        if board[row][col - 1] == None:
            adj_unknowns.append(row * n_cols + col - 1)
        elif board[row][col - 1] < 0:
            mines.append(row * n_cols + col - 1)
    if not last_col:
        if board[row][col + 1] == None:
            adj_unknowns.append(row * n_cols + col + 1)
        elif board[row][col + 1] < 0:
            mines.append(row * n_cols + col + 1)
    if not (last_row or first_col):
        if board[row + 1][col - 1] == None:
            adj_unknowns.append((row + 1) * n_cols + col - 1)
        elif board[row + 1][col - 1] < 0:
            mines.append((row + 1) * n_cols + col - 1)
    if not last_row:
        if board[row + 1][col] == None:
            adj_unknowns.append((row + 1) * n_cols + col)
        elif board[row + 1][col] < 0:
            mines.append((row + 1) * n_cols + col)
    if not (last_row or last_col):
        if board[row + 1][col + 1] == None:
            adj_unknowns.append((row + 1) * n_cols + col + 1)
        elif board[row + 1][col + 1] < 0:
            mines.append((row + 1) * n_cols + col + 1)
    return (adj_unknowns, mines)


# function to get clues
def get_clues(board):
    clues = []
    for i in range(len(board)):
        for j in range(len(board[i])):
            if board[i][j] != None and board[i][j] > 0:
                clues.append(i * len(board[i]) + j)
    return clues


# function to sort pairs
def sort_pairs(pairs):
    if len(pairs) > 1:
        mid = len(pairs) // 2
        left = pairs[:mid]
        right = pairs[mid:]

        sort_pairs(left)
        sort_pairs(right)

        i = j = k = 0

        # Copy data to temp arrays L[] and R[]
        while i < len(left) and j < len(right):
            if left[i][0] < right[j][0]:
                pairs[k] = left[i]
                i += 1
            elif left[i][0] > right[j][0]:
                pairs[k] = right[j]
                j += 1
            else:
                if left[i][1] < right[j][1]:
                    pairs[k] = left[i]
                    i += 1
                else:
                    pairs[k] = right[j]
                    j += 1
            k += 1

        # Checking if any element was left
        while i < len(left):
            pairs[k] = left[i]
            i += 1
            k += 1

        while j < len(right):
            pairs[k] = right[j]
            j += 1
            k += 1
    return pairs


# function to check if a clause contains a value
def has_compliment(a, b):
    x, = a
    for val in b:
        if val == x * -1:
            return True
    return False


# function to turn disjunction of conjuctions into a conjuction of disjunctions
def distribute(disjunct):
    added = set([])
    next = set([])
    sets = []
    for val in disjunct:
        sets.append(val)
    if len(sets) == 0:
        raise ValueError('No clauses given!')
    else:
        recurse_comb(next, sets, added)
    return added


# function to recursively loop through elements
def recurse_comb(next, sets, added):
    if len(sets) == 1:
        for r in sets[0]:
            tmp = next.copy()
            tmp.add(r)
            fs = frozenset(tmp)
            if not set_already_added(fs, added):
                added.add(fs)
    else:
        for r in sets[0]:
            tmp = next.copy()
            tmp.add(r)
            recurse_comb(tmp, sets[1:], added)


# function to check if a set has already been added to a list
def set_already_added(set, added):
    # go through list of already added, and check differences
    for a in added:
        diff1 = set.difference(a)
        diff2 = a.difference(set)
        if diff1 == diff2 and diff1 == 0:
            return True
    return False


# function to run checks on kb
def run_checks(reso_kb, tmp_kb, to_check):
    while not to_check.empty():
        x = to_check.get()
        if len(reso_kb) == 0:
            return False
        elif len(reso_kb) == 1:
            clause = reso_kb.pop()
            if x.issubset(clause):
                return False
            if len(x) == 1 and len(clause) == 1:
                first, = x
                first_comp = first * -1
                return first_comp in clause
            return False
        for clause in reso_kb:
            if x.issubset(clause):
                pass
            elif len(x) == 1:
                first, = x
                first_comp = first * -1
                fs = frozenset({first_comp})
                if len(clause.difference(fs)) == 0:
                    return True
                if first_comp in clause:
                    less_c = clause.difference(fs)
                    tmp_kb.add(less_c)
                    to_check.put(less_c)
                else:
                    tmp_kb.add(clause)
            else:
                tmp_kb.add(clause)
        tmp_kb.add(x)
        reso_kb = tmp_kb.copy()
        tmp_kb.clear()
        for i in range(to_check.qsize()):
            clause = to_check.get()
            if not x.issubset(clause):
                to_check.put(clause)
    return False


# generator function
def get_ms_gen(n_rows, n_cols, value):
    # make a blank board
    board = get_new_board(n_rows, n_cols)
    # create a KnowledgeBase
    kb = KnowledgeBase()
    save_val = value
    try:
        while True:
            value = (yield value)
            board = get_new_board(n_rows, n_cols, board, save_val, value)
            vars = get_vars(board)
            knowledge = knowledge_from_vars(vars)
            for clause in knowledge:
                kb.tell(clause)
            # find first safe spot
            i = 0
            no_safe_found = True
            while no_safe_found and i < n_cols * n_rows:
                board_val = board[i // n_cols][i % n_cols]
                if board_val == None:
                    # ask with a one-indexed value
                    if kb.ask((i + 1) * -1):
                        value = i + 1
                        save_val = value
                        no_safe_found = False
                i += 1

    finally:
        return


# function to extract knowledge from vars
def knowledge_from_vars(vars):
    knowledge = set([])
    # for each var
    for var in vars:
        # get c_dicts
        list_of_c_dicts = vars[var]
        disjunct = set([])
        # for each c_dict create a disjunction of conjunctions to distribute
        for c_dict in list_of_c_dicts:
            conjunct = []
            for index in c_dict:
                if c_dict[index]:
                    conjunct.append(index + 1)
                else:
                    conjunct.append((index + 1) * -1)
            disjunct.add(tuple(conjunct))
        # distribute disjunctions to get CNF form
        cnf = distribute(frozenset(disjunct))
        # update knowledge set
        knowledge.update(cnf)
    return knowledge


# function to get new board given clue
def get_new_board(n_rows, n_cols, board = None, index = 0, clue = None):
    rows = []
    for i in range(n_rows):
        row = []
        for j in range(n_cols):
            if board == None:
                row.append(None)
            elif (i * n_cols + j + 1) == index:
                row.append(clue)
            else:
                row.append(board[i][j])
        rows.append(tuple(row))
    return tuple(rows)


# function to get generator to give next move
def solve(n_rows, n_cols):
    return get_ms_gen(n_rows, n_cols, 1)


# class to represent a knowledge base for a minesweeper board
class KnowledgeBase():
    # knowledge base object
    knowledge = None

    # constructor method
    # Initialize an empty set of clauses, to be updated with the tell method
    def __init__(self):
        self.knowledge = set([])

    # method to add a given clause to the instance's set
    # clause: FrozenSet[int]
    # returns None
    def tell(self, clause):
        reso_kb = self.knowledge.copy()
        tmp_kb = set([])
        to_check = queue.Queue()
        to_check.put(clause)
        while not to_check.empty():
            x = to_check.get()
            for clause in reso_kb:
                if x.issubset(clause):
                    pass
                elif len(x) == 1:
                    first, = x
                    first_comp = first * -1
                    fs = frozenset({first_comp})
                    if first_comp in clause:
                        less_c = clause.difference(fs)
                        tmp_kb.add(less_c)
                        to_check.put(less_c)
                    else:
                        tmp_kb.add(clause)
                else:
                    tmp_kb.add(clause)
            tmp_kb.add(x)
            reso_kb = tmp_kb.copy()
            tmp_kb.clear()
            for i in range(to_check.qsize()):
                clause = to_check.get()
                if not x.issubset(clause):
                    to_check.put(clause)
        self.knowledge = reso_kb.copy()



    # determine whether the given index is safe using resolution
    # kb = [{-3, 2, 3}, {2, 4}, {2, 5, 6}]
    # returns a Boolean
    def ask(self, query):
        if len(self.knowledge) == 0:
            return True
        # create temporary kb's
        reso_kb = self.knowledge.copy()
        tmp_kb = set([])
        to_check = queue.Queue()
        to_check.put(frozenset({query * -1}))
        return run_checks(reso_kb, tmp_kb, to_check)
