# Sanity check of the trusted definitions in Defs.lean: vtxCode / faceIdx.
# Each triple must be three mutually adjacent vertices (edge length 2); in the icosahedron
# graph the 3-cliques are exactly the 20 faces.
import itertools
import math

phi = (1 + math.sqrt(5)) / 2
code = [
    [(0, 0), (1, 0), (0, 1)], [(1, 0), (0, 1), (0, 0)], [(0, 1), (0, 0), (1, 0)],
    [(0, 0), (1, 0), (0, -1)], [(1, 0), (0, -1), (0, 0)], [(0, 1), (0, 0), (-1, 0)],
    [(0, 0), (-1, 0), (0, 1)], [(-1, 0), (0, 1), (0, 0)], [(0, -1), (0, 0), (1, 0)],
    [(0, 0), (-1, 0), (0, -1)], [(-1, 0), (0, -1), (0, 0)], [(0, -1), (0, 0), (-1, 0)]]
V = [[a + b * phi for (a, b) in v] for v in code]
faces = [(0, 1, 2), (0, 1, 7), (0, 2, 6), (0, 6, 8), (0, 7, 8), (1, 2, 5), (1, 3, 5), (1, 3, 7),
         (2, 4, 5), (2, 4, 6), (3, 5, 9), (3, 7, 11), (3, 9, 11), (4, 5, 9), (4, 6, 10),
         (4, 9, 10), (6, 8, 10), (7, 8, 11), (8, 10, 11), (9, 10, 11)]


def d(i, j):
    return math.dist(V[i], V[j])


edges = {(i, j) for i, j in itertools.combinations(range(12), 2) if abs(d(i, j) - 2) < 1e-9}
cliques = {t for t in itertools.combinations(range(12), 3)
           if all(p in edges for p in itertools.combinations(t, 2))}
print("vertices distinct:", len({tuple(round(x, 9) for x in v) for v in V}) == 12)
print("edges:", len(edges), "(expected 30)")
print("3-cliques:", len(cliques), "(expected 20)")
print("faceIdx == 3-cliques:", set(faces) == cliques, "| distinct:", len(set(faces)) == 20)
