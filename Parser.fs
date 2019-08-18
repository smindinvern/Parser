namespace Parser

open Utils
open Zipper
open State

open Types

module Primitives =
    
    let inline get<'T, 'U> : Parser<'T, 'U, 'U> =
        State.get >>= fun (_, u, _) -> Monad.inject u
    let inline modify (f: 'U -> 'U) : Parser<'T, 'U, unit> =
        State.modify (fun (s, u, a) -> (s, f u, a))
        >>= (State.inject << Result.Ok)
    let set (u: 'U) : Parser<'T, 'U, unit> =
        modify (konst u)

    /// <summary>
    /// Encapsulate a Result value within a Parser.  The resulting Parser
    /// will either produce a value, or an error, according to the value
    /// of the given Result.
    /// </summary>
    /// <param name="r">The Result value to inject.</param>
    let inline liftResult (r: Result<'a, string>) : Parser<'T, 'U, 'a> =
        State.inject r
    
    /// <summary>
    /// Return the next token in the stream without consuming it.
    ///
    /// Produces an error if there are no more tokens in the stream.
    /// </summary>
    let inline peek<'T, 'U> : Parser<'T, 'U, 'T> =
        State.state {
            let! (ts, _, _) = State.get
            return! liftResult <| Zipper.get ts
        }

    open Monad

    /// <summary>
    /// Return the next token in the stream, and advance the stream by one.
    ///
    /// Produces an error if there are no more tokens in the stream.
    /// </summary>
    let inline pop<'T, 'U> : Parser<'T, 'U, 'T> =
        State.state {
            let! (ts, u, abort) = State.get
            return! parse {
                let! t = liftResult <| Zipper.get ts
                let! ts' = liftResult (ts .> 1)
                let! _ = State.(<@>) Result.Ok (State.put (ts', u, abort))
                return t
            }
        }

    /// <summary>
    /// Return the next n tokens in the stream, and advance the stream by n.
    ///
    /// Produces an error if there are fewer than n tokens in the stream.
    /// </summary>
    /// <param name="n">The number of tokens to pop.</param>
    let rec popN (n: int) : Parser<'T, 'U, 'T list> =
        if n = 0 then
            inject []
        else
            Utils.cons <@> pop <*> (popN (n - 1))

    /// <summary>
    /// Rewind the stream by one.
    ///
    /// Produces an error if the stream is already at its initial position.
    /// </summary>
    let push<'T, 'U> : Parser<'T, 'U, unit> =
        State.state {
            let! (ts, u, abort) = State.get
            return! parse {
                let! ts' = liftResult (ts <. 1)
                let! _ = State.(<@>) Result.Ok (State.put (ts', u, abort))
                return ()
            }
        }

    /// <summary>
    /// Rewind the stream by n.
    ///
    /// Produces an error if the stream cannot be rewound by n, i.e. if evaluating
    /// push n times would fail.
    /// </summary>
    /// <param name="n">The number of tokens to push.</param>
    let pushN (n: int) : Parser<'T, 'U, unit> =
        State.state {
            let! (ts, u, abort) = State.get
            return! parse {
                let! ts' = liftResult (ts <. n)
                let! _ = State.(<@>) Result.Ok (State.put (ts', u, abort))
                return ()
            }
        }

    /// <summary>
    /// Return the next n tokens in the stream.
    ///
    /// Produces an error if fewer than n tokens are remaining in the stream.
    /// </summary>
    /// <param name="n"></param>
    let peekN (n: int) =
        parse {
            if n = 0 then
                return []
            else
                let! toks = popN n
                let! _ = pushN n
                return toks
        }

    /// <summary>
    /// Consume a token and discard its value.
    ///
    /// Produces an error if there are no more tokens remaining in the stream.
    /// </summary>
    let inline discard<'T, 'U> =
        ignore <@> pop<'T, 'U>

    /// <summary>
    /// Consume n tokens and discard their values.
    ///
    /// Produces an error if there are fewer than n tokens remaining in the stream.
    /// </summary>
    /// <param name="n"></param>
    let rec discardN (n: int) =
        if n = 0 then
            inject ()
        else
            bind (fun _ -> discardN (n-1)) discard
    
    /// <summary>
    /// Produce an error from a given message and the current line number.
    ///
    /// Parsing may still continue via back-tracking.
    /// </summary>
    /// <param name="message">The error message.</param>
    let inline error (message: string) : Parser<'s, 'u, 'a> =
        liftResult << Result.Error <| message

    /// <summary>
    /// Terminate parsing immediately, producing an error.
    /// </summary>
    /// <param name="msg">The error message.</param>
    let abort (msg: string) : Parser<'s, 'u, 'a> =
        State.state {
            let! _ = State.modify (fun (ts, u, _) -> (ts, u, true))
            return! error msg
        }
    /// <summary>
    /// Attempt to evaluate and return value.  If the evaluation throws an exception, produce
    /// an error containing the Message property of the exception.
    /// </summary>
    /// <param name="v">The value to evaluate.</param>
    let inline catch (v: Lazy<'a>) =
        try
            inject <| v.Force()
        with
            | x -> error <| x.Message

    /// <summary>
    /// Run a parser on a given token stream and return the result.
    /// </summary>
    /// <param name="m">The parser to run.</param>
    /// <param name="s">The token stream to run it on.</param>
    let runParser (m: Parser<'s, 'u, 'a>) (s: TokenStream<'s>) (u: 'u) =
        State.runState m (s, u, false)
    
    type CharParser<'u, 'a> = Parser<char, 'u, 'a>
    type StringParser<'u, 'a> = Parser<string, 'u, 'a>

    module LineInfo =

        type Parser<'s, 'u, 'a> = State.State<TokenStream<'s*int> * 'u * bool, Result<'a, string>>
        let inline lineNo<'T, 'U> : Parser<'T, 'U, int> =
            snd <@> peek
        // These definitions shadow some of those given above.
        let inline peek<'T, 'U> : Parser<'T, 'U, 'T> =
            fst <@> peek
        let inline pop<'T, 'U> : Parser<'T, 'U, 'T> =
            fst <@> pop
        let inline error (message: string) : Parser<'s, 'u, 'a> =
            parse {
                let! line_no = lineNo<'s, 'u>
                return! error (message + " on line " + (string line_no))
            }
        let inline abort (msg: string) : Parser<'s, 'u, 'a> =
            parse {
                let! line_no = lineNo<'s, 'u>
                return! abort (msg + " on line " + (string line_no))
            }
        
        type StringParser<'u, 'a> = Parser<string, 'u, 'a>
    
