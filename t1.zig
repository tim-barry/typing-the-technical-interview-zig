// Typing the technical interview
// https://aphyr.com/posts/342-typing-the-technical-interview
// https://github.com/insou22/typing-the-technical-interview-rust
const std = @import("std");
const expectEqual = std.testing.expectEqual;

inline fn nth_child(comptime n: comptime_int, comptime T: type) type {
    //return std.meta.FieldType(T, .a);
    return @typeInfo(T).Struct.fields[n].field_type;
}

// We can't directly pattern-match on generics like Queen(A,B)
// so we use a hack: store the 'constructor'/'generic' function as a decl
// This is only necessary for Apply

// List
const Nil = struct {
    const ctor = Cons;
};
fn Cons(comptime X: type, comptime Xs: type) type {
    return struct {
        x: X,
        xs: Xs,
        const ctor = Cons;
    };
}

// precondition: T is list (Cons)
fn First(comptime T: type) type {
    //if (!(@hasDecl(T, "ctor") and T.ctor == Cons)) unreachable;
    return if (T == Nil) Nil else nth_child(0, T);
}
fn Second(comptime T: type) type {
    //if (!(@hasDecl(T, "ctor") and T.ctor == Cons)) unreachable;
    return if (T == Nil) Nil else nth_child(1, T);
}

// precondition: A, B are lists (Cons)
fn ListConcat(comptime A: type, comptime B: type) type {
    //if (!(@hasDecl(A, "ctor") and A.ctor == Cons)) unreachable;
    return if (A == Nil) B else Cons(First(A), ListConcat(Second(A), B));
}

fn ListConcatAll(comptime A: type) type {
    //if (!(@hasDecl(A, "ctor") and A.ctor == Cons)) unreachable;
    return if (A == Nil) Nil else ListConcat(First(A), ListConcatAll(Second(A)));
}
//test
//const L1 = Cons(N1, Nil);
//const L21 = Cons(N2, L1);
//const LL1L21 = Cons(L1, Cons(L21, Nil));
//const L121 = ListConcatAll(LL1L21);
//const L121b = Cons(N1, L21);

fn AnyTrue(comptime L: type) type {
    return if (L == Nil) False else if (First(L) == True) True else AnyTrue(Second(L));
}

const True = struct {};
const False = struct {};

fn Not(comptime A: type) type {
    //return if (A==True) False else if (A==False) True else unreachable;
    return switch (A) {
        True => False,
        False => True,
        else => unreachable,
    };
}
fn Or(comptime A: type, comptime B: type) type {
    return if (A == False and B == False) False else True;
}

const Z = struct {};
fn S(comptime T: type) type {
    return struct { x: T };
}
const N1 = S(Z);
const N2 = S(N1);
const N3 = S(N2);
const N4 = S(N3);
const N5 = S(N4);
const N6 = S(N5);
const N7 = S(N6);
const N8 = S(N7);
fn P(comptime T: type) type {
    return @typeInfo(T).Struct.fields[0].field_type;
}

fn PeanoEqual(comptime A: type, comptime B: type) type {
    return if (A == B) True else False;
}
fn PeanoLT(comptime A: type, comptime B: type) type {
    return if (B == Z) False else if (A == Z) True else PeanoLT(P(A), P(B));
}
fn PeanoAbsDiff(comptime A: type, comptime B: type) type {
    return if (B == Z) A else if (A == Z) B else PeanoAbsDiff(P(A), P(B));
}
test {
    comptime try expectEqual(PeanoLT(Z, Z), False);
    comptime try expectEqual(PeanoLT(S(Z), Z), False);
    comptime try expectEqual(PeanoLT(Z, S(Z)), True);
    comptime try expectEqual(PeanoLT(S(Z), S(Z)), False);
    comptime try expectEqual(PeanoLT(S(S(Z)), S(S(S(Z)))), True);
    comptime try expectEqual(PeanoLT(S(S(S(Z))), S(S(Z))), False);
    //comptime expectEqual(PeanoLT(Z,Z),False);
}
fn Range(comptime N: type) type {
    return if (N == Z) Nil else Cons(P(N), Range(P(N)));
}
test {
    comptime try expectEqual(Range(N6), Cons(N5, Cons(N4, Cons(N3, Cons(N2, Cons(N1, Cons(Z, Nil)))))));
}

fn Queen(comptime X: type, comptime Y: type) type {
    return struct {
        x: X,
        y: Y,
    };
}

fn AppendIf(comptime Pred: type, comptime x: type, comptime ys: type) type {
    return if (Pred == True) Cons(x, ys) else if (Pred == False) ys else unreachable;
}

// Queen threatens other queen
fn Threatens(comptime A: type, comptime B: type) type {
    //if (A.ctor != B.ctor) unreachable;
    const ax = nth_child(0, A);
    const ay = nth_child(1, A);
    const bx = nth_child(0, B);
    const by = nth_child(1, B);
    return Or(Or(PeanoEqual(ax, bx), PeanoEqual(ay, by)), PeanoEqual(PeanoAbsDiff(ax, bx), PeanoAbsDiff(ay, by)));
}

/// To be able to match Apply() for the correct partial application
/// have each partial store a reference to its constructor
/// Zig doesn't seem to have a way to directly pattern-match Type1(...types) like C++ templates do
const ctor_based = struct {
    fn Conj1(comptime L: type) type {
        return struct {
            l: L,
            const ctor = Conj1;
        };
    }

    fn Apply(comptime F: type, comptime N: type) type {
        //if (F.ctor != Conj1 and N == Nil) unreachable;
        return if (@typeInfo(F).Struct.fields.len == 1) switch (F.ctor) {
            Conj1 => Cons(N, nth_child(0, F)), //Note reversed
            Queen1 => Queen(nth_child(0, F), N),
            Threatens1 => Threatens(nth_child(0, F), N),
            Safe1 => Safe(nth_child(0, F), N),
            else => unreachable,
        } else if (@typeInfo(F).Struct.fields.len == 2) switch (F.ctor) {
            AddQueen2 => AddQueen(nth_child(0, F), nth_child(1, F), N),
            else => unreachable,
        } else unreachable;
    }

    fn Map(comptime F: type, comptime Xs: type) type {
        if (Xs == Nil) return Nil;
        //@compileLog(struct {}, F, Xs);
        const first = Apply(F, First(Xs));
        const rest = Map(F, Second(Xs));
        return Cons(first, rest);
        //return if (Xs == Nil) Nil else Cons(Apply(F, First(Xs)), Map(F, Second(Xs)));
    }
    fn MapCat(comptime F: type, comptime Xs: type) type {
        return if (Xs == Nil) Nil else ListConcatAll(Map(F, Xs));
    }
    fn Filter(comptime F: type, comptime Xs: type) type {
        return if (Xs == Nil) Nil else AppendIf(Apply(F, First(Xs)), First(Xs), Filter(F, Second(Xs)));
    }

    fn Queen1(comptime X: type) type {
        return struct {
            x: X,
            const ctor = Queen1;
        };
    }
    fn Threatens1(comptime A: type) type {
        return struct {
            a: A,
            const ctor = Threatens1;
        };
    }
    fn Safe1(comptime config: type) type {
        return struct {
            c: config,
            const ctor = Safe1;
        };
    }
    fn AddQueen2(comptime n: type, comptime x: type) type {
        return struct {
            tn: n,
            tx: x,
            const ctor = AddQueen2;
        };
    }

    fn QueensInRow(comptime N: type, comptime x: type) type {
        // A list of queens in row x with y from 0 to n.
        return Map(Queen1(x), Range(N));
    }

    fn Safe(comptime config: type, comptime queen: type) type {
        return Not(AnyTrue(Map(Threatens1(queen), config)));
    }
    fn AddQueen(comptime n: type, comptime x: type, comptime c: type) type {
        return Map(Conj1(c), Filter(Safe1(c), QueensInRow(n, x)));
    }
    fn AddQueenToAll(comptime n: type, comptime x: type, comptime cs: type) type {
        return MapCat(AddQueen2(n, x), cs);
    }
    fn AddQueensIf(comptime pred: type, comptime n: type, comptime x: type, comptime cs: type) type {
        return if (pred == False) cs else if (pred == True) AddQueens(n, S(x), AddQueenToAll(n, x, cs)) else unreachable;
    }
    fn AddQueens(comptime n: type, comptime x: type, comptime cs: type) type {
        return AddQueensIf(PeanoLT(x, n), n, x, cs);
    }
    fn Solution(comptime n: type) type {
        return First(AddQueens(n, Z, Cons(Nil, Nil)));
    }
};

/// Alternatively, the partial applications can purely store a closure
/// returning the full application
const closure_based = struct {
    fn Conj1(comptime L: type) type {
        return struct {
            fn Apply(comptime N: type) type {
                return Cons(N, L);
            }
        };
    }
    fn Queen1(comptime X: type) type {
        return struct {
            fn Apply(comptime Y: type) type {
                return Queen(X, Y);
            }
        };
    }
    fn Threatens1(comptime A: type) type {
        return struct {
            fn Apply(comptime B: type) type {
                return Threatens(A, B);
            }
        };
    }
    fn Safe1(comptime config: type) type {
        return struct {
            fn Apply(comptime B: type) type {
                return Safe(config, B);
            }
        };
    }
    fn AddQueen2(comptime n: type, comptime x: type) type {
        return struct {
            fn Apply(comptime B: type) type {
                return AddQueen(n, x, B);
            }
        };
    }
    // delegate to the closure
    fn Apply(comptime F: type, comptime N: type) type {
        return F.Apply(N);
    }

    // All other functions are the same

    fn Map(comptime F: type, comptime Xs: type) type {
        if (Xs == Nil) return Nil;
        const first = Apply(F, First(Xs));
        const rest = Map(F, Second(Xs));
        return Cons(first, rest);
    }
    fn MapCat(comptime F: type, comptime Xs: type) type {
        return if (Xs == Nil) Nil else ListConcatAll(Map(F, Xs));
    }

    fn Filter(comptime F: type, comptime Xs: type) type {
        return if (Xs == Nil) Nil else AppendIf(Apply(F, First(Xs)), First(Xs), Filter(F, Second(Xs)));
    }

    fn QueensInRow(comptime N: type, comptime x: type) type {
        // A list of queens in row x with y from 0 to n.
        return Map(Queen1(x), Range(N));
    }

    fn Safe(comptime config: type, comptime queen: type) type {
        return Not(AnyTrue(Map(Threatens1(queen), config)));
    }
    fn AddQueen(comptime n: type, comptime x: type, comptime c: type) type {
        return Map(Conj1(c), Filter(Safe1(c), QueensInRow(n, x)));
    }
    fn AddQueenToAll(comptime n: type, comptime x: type, comptime cs: type) type {
        return MapCat(AddQueen2(n, x), cs);
    }
    fn AddQueensIf(comptime pred: type, comptime n: type, comptime x: type, comptime cs: type) type {
        return if (pred == False) cs else if (pred == True) AddQueens(n, S(x), AddQueenToAll(n, x, cs)) else unreachable;
    }
    fn AddQueens(comptime n: type, comptime x: type, comptime cs: type) type {
        return AddQueensIf(PeanoLT(x, n), n, x, cs);
    }
    fn Solution(comptime n: type) type {
        return First(AddQueens(n, Z, Cons(Nil, Nil)));
    }
};

test {
    const sol1 = comptime blk: {
        @setEvalBranchQuota(500_000);
        break :blk ctor_based.Solution(N8);
    };
    const sol2 = comptime blk: {
        @setEvalBranchQuota(1000_000);
        break :blk closure_based.Solution(N8);
    };
    try expectEqual(sol1, sol2);
    std.debug.print("{s}\n", .{@typeName(sol1)});
}
