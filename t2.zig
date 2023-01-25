// Typing the technical interview
// https://aphyr.com/posts/342-typing-the-technical-interview
// https://github.com/insou22/typing-the-technical-interview-rust
const std = @import("std");
const expectEqual = std.testing.expectEqual;

/// Convenience
inline fn nth_child(comptime n: comptime_int, comptime T: type) type {
    return @typeInfo(T).Struct.fields[n].field_type;
}

// This version, instead of having functions that branch on their inputs,
// delegates (most) branching to the type system, by implementing many functions
// as methods instead on the corresponding base values (Nil/Cons, True/False, Queen...)

// List
const Nil = struct {
    fn First() type {
        return Nil;
    }
    fn Second() type {
        return Nil;
    }
    fn ListConcat(comptime B: type) type {
        return B;
    }
    fn ListConcatAll() type {
        return Nil;
    }
    fn AnyTrue() type {
        return False;
    }
};
fn Cons(comptime X: type, comptime Xs: type) type {
    return struct {
        // x: X,  xs: Xs,
        fn First() type {
            return X;
        }
        fn Second() type {
            return Xs;
        }
        fn ListConcat(comptime B: type) type {
            return Cons(X, Xs.ListConcat(B));
        }
        fn ListConcatAll() type {
            return X.ListConcat(Xs.ListConcatAll());
        }
        fn AnyTrue() type {
            return if (X == True) True else Xs.AnyTrue();
        }
    };
}

const True = struct {
    fn Not() type {
        return False;
    }
    fn Or(comptime B: type) type {
        _ = B;
        return True;
    }
    fn AppendIf(comptime x: type, comptime ys: type) type {
        return Cons(x, ys);
    }
    fn AddQueensIf(comptime n: type, comptime x: type, comptime cs: type) type {
        return AddQueens(n, S(x), AddQueenToAll(n, x, cs));
    }
};
const False = struct {
    fn Not() type {
        return True;
    }
    fn Or(comptime B: type) type {
        return B;
    }
    fn AppendIf(comptime x: type, comptime ys: type) type {
        _ = x;
        return ys;
    }
    fn AddQueensIf(comptime n: type, comptime x: type, comptime cs: type) type {
        _ = n;
        _ = x;
        return cs;
    }
};

const Z = struct {
    /// Convenience, avoid "if (B==Z) True else False"
    fn IsZ() type {
        return True;
    }
    //fn P() type {
    //    return Z;
    //}
    fn PeanoEqual(comptime B: type) type {
        return B.IsZ(); // if (B == @This()) True else False
    }
    fn PeanoLT(comptime B: type) type {
        return B.IsZ().Not();
    }
    fn PeanoAbsDiff(comptime B: type) type {
        return B;
    }
    fn Range() type {
        return Nil;
    }
};
fn S(comptime T: type) type {
    return struct {
        // x: T,
        /// Convenience
        fn IsZ() type {
            return False;
        }
        fn P() type {
            return T;
        }
        fn PeanoEqual(comptime B: type) type {
            // optimization, actual something like
            // return if (B==Z) False else T.PeanoEqual(B.P());
            return if (B == @This()) True else False;
        }
        fn PeanoLT(comptime B: type) type {
            return if (B == Z) False else T.PeanoLT(B.P());
        }
        fn PeanoAbsDiff(comptime B: type) type {
            return if (B == Z) @This() else T.PeanoAbsDiff(B.P());
        }
        fn Range() type {
            return Cons(T, T.Range());
        }
    };
}
const N1 = S(Z);
const N2 = S(N1);
const N3 = S(N2);
const N4 = S(N3);
const N5 = S(N4);
const N6 = S(N5);
const N7 = S(N6);
const N8 = S(N7);

test "Peano integers" {
    comptime try expectEqual(Z.PeanoLT(Z), False);
    comptime try expectEqual(N1.PeanoLT(Z), False);
    comptime try expectEqual(Z.PeanoLT(N1), True);
    comptime try expectEqual(N1.PeanoLT(N1), False);
    comptime try expectEqual(N2.PeanoLT(N3), True);
    comptime try expectEqual(N3.PeanoLT(N2), False);
    comptime try expectEqual(N6.Range(), Cons(N5, Cons(N4, Cons(N3, Cons(N2, Cons(N1, Cons(Z, Nil)))))));
}

fn Queen(comptime X: type, comptime Y: type) type {
    return struct {
        x: X,
        y: Y,
        // Queen threatens other queen
        fn Threatens(comptime B: type) type {
            const bx = nth_child(0, B);
            const by = nth_child(1, B);
            return X.PeanoEqual(bx).Or(Y.PeanoEqual(by)).Or(X.PeanoAbsDiff(bx).PeanoEqual(Y.PeanoAbsDiff(by)));
        }
    };
}

// Partial data types just store the closure for full type
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
        const Apply = A.Threatens;
        //fn Apply(comptime B: type) type {
        //    return A.Threatens(B);
        //}
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

fn Map(comptime F: type, comptime Xs: type) type {
    if (Xs == Nil) return Nil;
    const first = F.Apply(Xs.First());
    const rest = Map(F, Xs.Second());
    return Cons(first, rest);
}
fn MapCat(comptime F: type, comptime Xs: type) type {
    return if (Xs == Nil) Nil else Map(F, Xs).ListConcatAll();
}
fn Filter(comptime F: type, comptime Xs: type) type {
    return if (Xs == Nil) Nil else F.Apply(Xs.First()).AppendIf(Xs.First(), Filter(F, Xs.Second()));
}

fn QueensInRow(comptime N: type, comptime x: type) type {
    // A list of queens in row x with y from 0 to n.
    return Map(Queen1(x), N.Range());
}

fn Safe(comptime config: type, comptime queen: type) type {
    return Map(Threatens1(queen), config).AnyTrue().Not();
}
fn AddQueen(comptime n: type, comptime x: type, comptime c: type) type {
    return Map(Conj1(c), Filter(Safe1(c), QueensInRow(n, x)));
}
fn AddQueenToAll(comptime n: type, comptime x: type, comptime cs: type) type {
    return MapCat(AddQueen2(n, x), cs);
}
fn AddQueens(comptime n: type, comptime x: type, comptime cs: type) type {
    return x.PeanoLT(n).AddQueensIf(n, x, cs);
}
fn Solution(comptime n: type) type {
    return AddQueens(n, Z, Cons(Nil, Nil)).First();
}

const sol = blk: {
    // Even N4 exceeds the default limit of 1000
    // so since we need to manually set a higher quota anyway
    // there's no particular reason not to go all the way to N8
    //@setEvalBranchQuota(30_000);
    //break :blk Solution(N6); // ~1.4 sec
    @setEvalBranchQuota(500_000);
    break :blk Solution(N8); // ~3.4 sec
};
test {
    std.debug.print("{s}\n", .{@typeName(sol)});
}
pub fn main() void {
    std.debug.print("{s}\n", .{@typeName(sol)});
}
