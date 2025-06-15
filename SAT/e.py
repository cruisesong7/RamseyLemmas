import pysat.solvers
import pysat.card
import itertools
import argparse
import sys

def eij(i, j):
    assert(i > j)

    return i * (i - 1) // 2 + j + 1

def output_clauses(n, k, pol):
    clauses = []
    
    for c in itertools.combinations(list(range(n)), k):
        clauses.append([(1 if pol else -1) * eij(e[1], e[0]) for e in itertools.combinations(c, 2)])

    return clauses

if __name__ == "__main__":
    a = argparse.ArgumentParser(description="Generate formulas for e(x,y,n,≤e)")

    a.add_argument("--pb", action="store_true", default=False, help="Encode as a pseudo-Boolean formula")
    a.add_argument("--enc", type=int, choices=[pysat.card.EncType.__dict__[k] for k in vars(pysat.card.EncType).keys() if not k.startswith("__")], help="Encoder type (%s)" % ", ".join(["%s=%d" % (k, pysat.card.EncType.__dict__[k]) for k in vars(pysat.card.EncType).keys() if not k.startswith("__")]), default=1)
    a.add_argument("x", type=int, help="Avoid cliques of order x")
    a.add_argument("y", type=int, help="Avoid independent sets of order y")
    a.add_argument("n", type=int, help="Order of the graph")
    a.add_argument("e", type=int, help="Upper-bound on the size of the graph")

    res = a.parse_args()
    
    if res.pb:
        pos_clauses = output_clauses(res.n, res.y, True)
        neg_clauses = output_clauses(res.n, res.x, True)
        
        print("* #variable= %d #constraint= %d" % (res.n * (res.n - 1) // 2, len(pos_clauses) + len(neg_clauses) + 1))

        for c in pos_clauses:
            print(" ".join(["+1 x%d" % l for l in c]), ">= 1;")

        for c in neg_clauses:
            print(" ".join(["+1 ~x%d" % l for l in c]), ">= 1;")

        print(" ".join(["-1 x%d" % eij(j, i) for i, j in itertools.combinations(list(range(res.n)), 2)]), " >= -%d;" % res.e)
    else:
        f = pysat.card.CardEnc.atmost([eij(e[1], e[0]) for e in itertools.combinations(list(range(res.n)), 2)], bound=res.e)

        f.extend(output_clauses(res.n, res.y, True))
        f.extend(output_clauses(res.n, res.x, False))

        # You may ask "why not just print f.to_dimacs()?". Don't.
        print("p cnf", f.nv, len(f.clauses))

        for c in f.clauses:
            print(" ".join([str(l) for l in c]), "0")

        # print ("p cnf", res.n * (res.n - 1) // 2, len(pos_clauses) + len(neg_clauses))

        # s = pysat.solvers.Solver(bootstrap_with=pos_clauses + neg_clauses)
        # b = res.n * (res.n - 1) // 2

        # for m in s.enum_models():
        #     newb = len([l for l in m if l > 0])

        #     if newb < b:
        #         b = newb
        #         print("b = ", b)
