namespace smindinvern.Parser

module Combinators =

    open Utils
    open Types
    open Monad
    open Primitives
    
    /// <summary>
    /// Parse something, ignore something else.  Useful for eating non-semantic tokens, e.g. commas.
    ///
    /// This parser fails if either of the given parsers fail.
    /// </summary>
    /// <param name="keep">Parser for the value to keep.</param>
    /// <param name="skip">Parser for the bits to skip.</param>
    let inline (<!>) (keep: Parser<'T, 'U, 'a>) (skip: Parser<'T, 'U, 'b>) : Parser<'T, 'U, 'a> =
        parse {
            let! keep' = keep
            let! _ = skip
            return keep'
        }
    
    /// <summary>
    /// Models short-circuit logical-OR on Parsers.
    ///
    /// (f <|> g) produces a value IFF one of the two parsers succeeds.
    /// If both parsers fail, their errors are concatenated around the
    /// string " <|> " to indicate that alternatives were attempted.
    /// </summary>
    /// <param name="f">The first parser to try.</param>
    /// <param name="g">The second parser to try.</param>
    let (<|>) (f: Parser<'s, 'u, 'a>) (g: Parser<'s, 'u, 'a>) : Parser<'s, 'u, 'a> =
        // Implement choice with possibility of failure
        State.state {
            let! s = State.get
            match! f with
            | Result.Error msg1 ->
                let! (_, _, abort) = State.get
                if abort then
                    return Result.Error msg1
                else
                    // Back-track to previous state.
                    let! _ = State.put s
                    match! g with
                    | Result.Error msg2 -> return Result.Error (msg1 + " <|> " + msg2)
                    | x -> return x
            | x -> return x
        }
    
    /// <summary>
    /// Try each parser in a list until one succeeds.  Produce an error otherwise.
    /// </summary>
    /// <param name="ps">A list of parsers to try.</param>
    let inline oneOf (ps: Parser<'s, 'u, 'a> list) : Parser<'s, 'u, 'a> =
        Utils.fold' (<|>) ps
    
    /// <summary>
    /// Attempt to run a parser.  If it fails, produce a given "default" value,
    /// rather than an error.
    /// </summary>
    /// <param name="c">The parser to run.</param>
    /// <param name="def">The value to produce in case of error.</param>
    let inline optional (c: Parser<'s, 'u, 'a>) (def: 'a) : Parser<'s, 'u, 'a> =
        c <|> (inject def)
    
    /// <summary>
    /// Run a parser, mapping errors to Option.None.
    ///
    /// This parser always succeeds.
    /// </summary>
    /// <param name="c">The parser to try.</param>
    let inline tryParse (c: Parser<'s, 'u, 'a>) : Parser<'s, 'u, 'a option> =
        optional (Option.Some <@> c) Option.None

    let rec private parseUntilTailRecursive (p: Parser<'s, 'u, bool>) (c: Parser<'s, 'u, 'a>) (tail: 'a list) : Parser<'s, 'u, 'a list> =
        parse {
            let! b = p
            if b then
                return List.rev tail
            else
                let! c' = c
                return! parseUntilTailRecursive p c (c'::tail)
        }
    
    /// <summary>
    /// Run a parser iteratively until the predicate p produces true, and return
    /// the results as a list.
    ///
    /// If at any time the predicate produces an error, this parser fails with that error.
    /// </summary>
    /// <param name="p">The predicate to test against at each iteration.</param>
    /// <param name="c">The parser to collect values from.</param>
    let parseUntil (p: Parser<'s, 'u, bool>) (c: Parser<'s, 'u, 'a>) : Parser<'s, 'u, 'a list> =
        parseUntilTailRecursive p c []
    
    let rec private parseUntilFailTailRecursive (c: Parser<'s, 'u, 'a>) (tail: 'a list) : Parser<'s, 'u, 'a list> =
        parse {
            match! tryParse c with
            | Option.None -> return List.rev tail
            | Option.Some x -> return! parseUntilFailTailRecursive c (x::tail)
        }
    
    /// <summary>
    /// Run a parser iteratively until it fails, and return the results as a list.
    ///
    /// This parser always succeeds.  In the case of immediate failure, an empty list
    /// is returned.
    /// </summary>
    /// <param name="c">The parser to run.</param>
    let some (c: Parser<'s, 'u, 'a>) : Parser<'s, 'u, 'a list> =
        parseUntilFailTailRecursive c []
    
    let inline many (c: Parser<'s, 'u, 'a>) : Parser<'s, 'u, 'a list> =
        Utils.cons <@> c <*> some c
    
    let inline repeat (c: Parser<'s, 'u, 'a>) (n: int) : Parser<'s, 'u, 'a list> =
        sequence <| List.replicate n c

    let rec atMost (c: Parser<'s, 'u, 'a>) (n:int) : Parser<'s, 'u, 'a list> =
        optional (Utils.cons <@> c <*> (atMost c (n - 1))) []
        
    let range (c: Parser<'s, 'u, 'a>) (atLeastN: int) (atMostN: int) : Parser<'s, 'u, 'a list> =
        parse {
            let! prefix = repeat c atLeastN
            let! rest = atMost c (atMostN - atLeastN)
            return prefix @ rest
        }

    let isEOF<'s, 'u> : Parser<'s, 'u, bool> =
        (konst false <@> peek1) <|> (inject true)
    
    let inline (<||>) p1 p2 =
        parse {
            match! p1 with
            | true -> return true
            | false -> return! p2
        }
    let inline (<&&>) p1 p2 =
        parse {
            match! p1 with
            | true -> return! p2
            | false -> return false
        }
    let inline (<=>) p1 p2 =
        (=) <@> p1 <*> p2

    module StringParser =
        let inline (<+>) (s1: StringParser<'u, 'a>) (s2: StringParser<'u, 'a>) =
            (+) <@> s1 <*> s2
        let inline (~%) (s: string) =
            parse {
                let! x = pop1
                if x = s then
                    return s
                else
                    return! error <| "Expecting \"" + s + "\""
            }

    module LineInfo =
        open Primitives.LineInfo
        
        module StringParser =
            let inline (<+>) (s1: StringParser<'u, 'a>) (s2: StringParser<'u, 'a>) =
                (+) <@> s1 <*> s2
            let inline (~%) (s: string) =
                parse {
                    let! x = pop1
                    if x = s then
                        return s
                    else
                        return! error <| "Expecting \"" + s + "\""
                }
