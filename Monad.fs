namespace smindinvern.Parser

module Monad =
    open Utils
    open State
    open Types

    let inline inject (v: 'a) : Parser<'T, 'U, 'a> =
        State.state {
            return Result.Ok v
        }
    let inline bind (f: 'a -> Parser<'T, 'U, 'b>) (c: Parser<'T, 'U, 'a>) =
        State.state {
            match! c with
            | Result.Error e -> return Result.Error e
            | Result.Ok a -> return! f a
        }

    let inline (>>=) m f = bind f m

    type Parser() =
        member inline __.Bind(m: Parser<'T, 'U, 'a>, f: 'a -> Parser<'T, 'U, 'b>) : Parser<'T, 'U, 'b> = m >>= f
        member inline __.Return(v: 'a) : Parser<'T, 'U, 'a> = inject v
        member inline __.ReturnFrom(m: Parser<'T, 'U, 'a>) = m
        member inline __.Combine(a: Parser<'T, 'U, unit>, b: Parser<'T, 'U, 'b>) : Parser<'T, 'U, 'b> =
            a >>= (konst b)

    let parse = Parser()

    /// <summary>
    /// Function application lifted into the Parser monad.
    ///
    /// Just as with normal function application, (<@>) is left-associative.
    /// </summary>
    let inline (<@>) (f: 'a -> 'b) (c: Parser<'T, 'U, 'a>) : Parser<'T, 'U, 'b> =
        bind (inject << f) c

    /// <summary>
    /// Function composition lifted into the Parser monad.
    ///
    /// Just as with normal function composition, (<*>) is associative, i.e.
    /// f <*> (g <*> h) = (f <*> g) <*> h
    /// </summary>

    let inline (<*>) (f: Parser<'T, 'U, 'a -> 'b>) (c: Parser<'T, 'U, 'a>) : Parser<'T, 'U, 'b> =
        bind (fun f' -> f' <@> c) f
    
    let sequence (cs: Parser<'T, 'U, 'a> list) : Parser<'T, 'U, 'a list> =
        List.foldBack (fun t s -> Utils.cons <@> t <*> s) cs (inject [])
