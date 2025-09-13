import sys
import re
import argparse

if __name__ == "__main__":
    parser = argparse.ArgumentParser("Strip PPR information from proofs")

    parser.add_argument("input", type=argparse.FileType('r'), help="Input proof")

    res = parser.parse_args()
    pivot = None

    print("pseudo-Boolean proof version 2.0")

    for l in res.input:
        if l.startswith("c") or l.startswith("d"):
            continue

        parts = [int(i) for i in l.strip().split()]
        sep = parts[0]

        if sep in parts[1:]:
            # this is a ppr line, turn it into a red line
            first_break = parts.index(sep, 1)
            second_break = parts.index(sep, first_break + 1)
            prclause = [int(i) for i in parts[:first_break]]

            # We are only dealing with clauses of the form -x y
            assert(len(prclause) == 2)

            if pivot is None:
                pivot = prclause[1]

            prpermutation = parts[second_break + 1:-1]
            line = ["x%d" % abs(pivot), "1", "x%d" % abs(prclause[0]), "0"] + ["x%s" % s for s in prpermutation]
            print("red +1 x%d +1 ~x%d >= 1;" % (prclause[1], abs(prclause[0])), " ".join(line), ";")
            print("+1 x%d +1 ~x%d >= 1;" % (prclause[1], abs(prclause[0])), file=sys.stderr)
        else:
            # this is a rup line
            print("rup +1 ~x%d >= 1;" % abs(int(parts[0])))
            print("+1 ~x%d >= 1;" % abs(int(parts[0])), file=sys.stderr)
            pivot = None

    print("""output EQUIOPTIMAL IMPLICIT
conclusion NONE
end pseudo-Boolean proof""")
