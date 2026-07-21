"""Author: Carles Marín.

Program: executable cross-check of the canonical-obstruction theory.

Input: a finite set-system presentation and a partial transversal I of it.
Output: the lattice of tight subsets of I, its maximum element maxTight(I), and an
        exhaustive check that `insert e I` is a partial transversal exactly when the
        compatible slots of e are not contained in N(maxTight(I)).
Verification status: auxiliary SageMath/Python check only; it is not a formal proof.
        The formal statements are `tight_union_and_inter`, `maxTight_isTight` and
        `insert_iff_not_subset_maxTight` in
        lean/Theorems/TransversalObstruction.lean.

Run with `sage check_canonical_obstruction.sage` or with plain `python3`; the script
uses no Sage-specific call, so both interpreters give the same output.
"""

from itertools import combinations, permutations

# The running example of the paper.  Five presenting sets over {a,b,c,d,x,y}; the
# compatible slots are N(a)={0,1}, N(b)={1}, N(c)={1,2}, N(d)={3,4}, N(x)={2}, N(y)={4}.
# It is chosen so that the tight subsets of I={a,b,c,d} form a genuine (non-chain)
# lattice and so that maxTight(I) is a proper subset of I.
EXAMPLE = [frozenset("a"), frozenset("abc"), frozenset("cx"),
           frozenset("d"), frozenset("dy")]


def subsets(elements):
    elements = sorted(elements)
    return [frozenset(choice) for size in range(len(elements) + 1)
            for choice in combinations(elements, size)]


def slots(family, element):
    """N({element}): the indices of the presenting sets containing `element`."""
    return frozenset(i for i, block in enumerate(family) if element in block)


def neighbourhood(family, subset):
    """N(S): the union of the compatible slots of the members of S."""
    return frozenset().union(*[slots(family, x) for x in subset]) if subset else frozenset()


def partial_transversal(family, chosen):
    chosen = tuple(sorted(chosen))
    if len(chosen) > len(family):
        return False
    return any(
        all(element in family[index] for element, index in zip(chosen, indices))
        for indices in permutations(range(len(family)), len(chosen))
    )


def is_tight(family, subset):
    return len(neighbourhood(family, subset)) == len(subset)


def tight_subsets(family, independent):
    return [S for S in subsets(independent) if is_tight(family, S)]


def max_tight(family, independent):
    tights = tight_subsets(family, independent)
    return frozenset().union(*tights) if tights else frozenset()


def report(family, independent):
    universe = sorted(set().union(*family))
    assert partial_transversal(family, independent), "I must be a partial transversal"
    tights = tight_subsets(family, independent)
    top = max_tight(family, independent)

    print("presentation      :", [sorted(block) for block in family])
    print("I                 :", sorted(independent))
    print("tight subsets of I:", [sorted(S) for S in tights])
    print("maxTight(I)       :", sorted(top), " N =", sorted(neighbourhood(family, top)))
    print("maxTight is tight :", is_tight(family, top))

    # Closure under union and intersection: the tight sets form a lattice.
    lattice = all(is_tight(family, R | S) and is_tight(family, R & S)
                  for R in tights for S in tights)
    print("lattice (union/intersection closed):", lattice)

    # maxTight is the maximum, not merely a maximal, tight set.
    print("every tight subset is below maxTight:", all(S <= top for S in tights))

    # The decision theorem, checked exhaustively on every candidate element.
    print("\n e | insert e I feasible | N(e) subset of N(maxTight) | agree")
    for e in universe:
        if e in independent:
            continue
        feasible = partial_transversal(family, independent | {e})
        covered = slots(family, e) <= neighbourhood(family, top)
        print(f" {e} | {str(feasible):>19} | {str(covered):>26} | {feasible != covered}")


def rank(family, subset):
    """Matroid rank of `subset`: the size of its largest partial-transversal subset."""
    subset = sorted(subset)
    for size in range(len(subset), -1, -1):
        for choice in combinations(subset, size):
            if partial_transversal(family, frozenset(choice)):
                return size
    return 0


def check_ore_defect_formula(family):
    """Check Ore's defect formula for the rank, exhaustively.

    r(X) = min over S subset of X of ( |X \\ S| + |N(S)| ).

    This is the formula the paper names as future work in Lean. It is NOT formalized;
    this exhaustive check on the running presentation is the only evidence offered for it,
    and the paper says so.
    """
    universe = sorted(set().union(*family))
    checked = 0
    for X in subsets(universe):
        lhs = rank(family, X)
        rhs = min(len(X - S) + len(neighbourhood(family, S)) for S in subsets(X))
        assert lhs == rhs, (sorted(X), lhs, rhs)
        checked += 1
    print(f"Ore defect formula r(X) = min_S (|X\\S| + |N(S)|): "
          f"verified on all {checked} subsets of the ground set.")


def exhaustive_check(family):
    """Check the decision theorem on every partial transversal and every element."""
    universe = sorted(set().union(*family))
    independents = [S for S in subsets(universe) if partial_transversal(family, S)]
    tested = 0
    for independent in independents:
        top = max_tight(family, independent)
        assert is_tight(family, top)
        for S in tight_subsets(family, independent):
            assert S <= top
        for e in universe:
            if e in independent:
                continue
            feasible = partial_transversal(family, independent | {e})
            covered = slots(family, e) <= neighbourhood(family, top)
            assert feasible != covered, (sorted(independent), e)
            tested += 1
    print(f"partial transversals: {len(independents)};"
          f" insertion decisions checked: {tested}; all agree with maxTight.")


if __name__ == "__main__":
    report(EXAMPLE, frozenset("abcd"))
    print()
    exhaustive_check(EXAMPLE)
    check_ore_defect_formula(EXAMPLE)
