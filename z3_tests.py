import z3


def main():
    h = z3.Bool('hungry')
    f = z3.Bool('food')
    w = z3.Bool('work')
    l = z3.Bool('leave')
    var = [h, f, w, l]

    solve = z3.Solver()

    solve.add(h == f)
    solve.add(z3.Or(*var))
    solve.add(z3.PbEq([(v, 1) for v in var], 1))

    print(solve)
    sat = solve.check()
    print(solve.model())

if __name__ == '__main__':
    main()