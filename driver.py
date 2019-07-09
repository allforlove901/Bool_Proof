import boolproof as bp
#
kb = bp.KnowledgeBase()
# kb.tell(frozenset({1, 2, 3}))
# kb.tell(frozenset({5, 2, 3}))
# kb.tell(frozenset({2, 8}))
# kb.tell(frozenset({5, -8}))
# kb.tell(frozenset({-5, 8}))
kb.tell(frozenset({5, -4}))
kb.tell(frozenset({4, 2}))
kb.tell(frozenset({-2, 5}))
# kb = set([frozenset({1, 2, 3}), frozenset({5, 6, 7}), frozenset({1, 0})])

# print(kb.ask(5))
board = ((0, None, None, None), (None, None, None, None), (None, None, None, None))
vars = bp.get_vars(board)
gen = bp.solve(4, 4)

bjord = [0, 0, 1, 1, 0, 0, 1, -1, 2, 3, 3, 2, -1, -1, -1, 1]
safe = next(gen)
i = 0
while i < 16:
    print("You say {} is safe".format(safe))
    if bjord[safe - 1] < 0:
        print("You said {} was safe but twasn't lad!".format(safe))
    safe = gen.send(bjord[safe - 1])
    i += 1
