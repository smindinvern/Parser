namespace smindinvern.Parser

open smindinvern.Utils
open smindinvern.Zipper

open Types

open System
open smindinvern.Alternative
open smindinvern.Alternative.Monad

module Primitives =

    let inline get<'T, 'U> : Parser<'T, 'U, 'U> =
        get >>= (fun (_, u) -> Monad.inject u)
    let inline modify (f: 'U -> 'U) : Parser<'T, 'U, unit> =
        modify (fun (t, u) -> (t, f u)) >>= Monad.inject
    let put (u: 'U) : Parser<'T, 'U, unit> =
        modify (konst u)

    let inline private getTokenStream<'T, 'U> : Parser<'T, 'U, TokenStream<'T>> =
        smindinvern.Alternative.get
        >>= fun (ts, _) -> Monad.inject ts
    let inline private putTokenStream<'T, 'U> (ts: TokenStream<'T>) : Parser<'T, 'U, unit> =
        smindinvern.Alternative.modify (fun (_, u) -> (ts, u))
        >>= Monad.inject

    module Results =
        open smindinvern.Alternative.Errors
        let liftResult r = liftResult <| Result.mapError (fun e -> { Tree.Value = e; Tree.Children = [] }) r

    open Results
    open Monad

    /// <summary>
    /// Return the next n tokens in the stream without consuming them.
    ///
    /// Produces an error if there are fewer than n tokens are remaining in the stream.
    /// </summary>
    /// <param name="n">The number of tokens to return.</param>
    let peek<'T, 'U> (n: int) : Parser<'T, 'U, 'T list> =
        let getToken zr tokens =
            let consToList (t: 'T) =
                Result.map (List.cons t) tokens
            let tr = Result.bind Zipper.get zr
            Result.bind consToList tr
        parse {
            if n = 0 then
                return []
            else
            let! ts = getTokenStream
            let zippers = [ for i in 0..(n-1) -> (ts .> i) ]
            let toks = List.foldBack getToken zippers (Result.Ok [])
            return! liftResult toks
        }

    /// <summary>
    /// Return the next token in the stream without consuming it.
    ///
    /// Produces an error if there are no more tokens in the stream.
    /// </summary>
    /// <remarks>Equivalent to <c>peek 1</c>.</remarks>
    /// <seealso cref="peek"/>
    let inline peek1<'T, 'U> : Parser<'T, 'U, 'T> =
        getTokenStream
        >>= (liftResult << Zipper.get)

    /// <summary>
    /// Consume n tokens and discard their values.
    ///
    /// Produces an error if there are fewer than n tokens remaining in the stream.
    /// </summary>
    /// <param name="n">The number of tokens to discard.</param>
    let discard<'T, 'U> (n: int) : Parser<'T, 'U, unit> =
        parse {
            let! ts = getTokenStream
            let! ts' = liftResult (ts .> n)
            return! putTokenStream ts'
        }

    /// <summary>
    /// Consume a token and discard its value.
    ///
    /// Produces an error if there are no more tokens remaining in the stream.
    /// </summary>
    /// <remarks>Equivalent to <c>discard 1</c>.</remarks>
    /// <seealso cref="discard"/>
    let inline discard1<'T, 'U> : Parser<'T, 'U, unit> =
        discard 1

    /// <summary>
    /// Consume the next n tokens in the stream and return their values.
    ///
    /// Produces an error if there are fewer than n tokens in the stream.
    /// </summary>
    /// <param name="n">The number of tokens to pop.</param>
    let rec pop<'T, 'U> (n: int) : Parser<'T, 'U, 'T list> =
        parse {
            let! tokens = peek n
            do! discard n
            return tokens
        }

    /// <summary>
    /// Consume the next token in the stream and return its value.
    ///
    /// Produces an error if there are no more tokens in the stream.
    /// </summary>
    /// <remarks>Equivalent to <c>pop 1</c>.</remarks>
    /// <seealso cref="pop"/>
    let inline pop1<'T, 'U> : Parser<'T, 'U, 'T> =
        parse {
            let! ts = getTokenStream
            let! token = liftResult <| Zipper.get ts
            let! ts' = liftResult (ts .> 1)
            do! putTokenStream ts'
            return token
        }

    /// <summary>
    /// Rewind the stream by n tokens.
    ///
    /// Produces an error if the stream cannot be rewound by n, i.e. if fewer than
    /// n tokens have been consumed so far.
    /// </summary>
    /// <param name="n">The number of tokens to rewind.</param>
    let rewind (n: int) : Parser<'T, 'U, unit> =
        parse {
            let! ts = getTokenStream
            let! ts' = liftResult (ts .> n)
            return! putTokenStream ts'
        }

    /// <summary>
    /// Rewind the stream by one token.
    ///
    /// Produces an error if the stream is already at its initial position.
    /// </summary>
    /// <remarks>Equivalent to <c>rewind 1</c>.</remarks>
    /// <seealso cref="rewind"/>
    let rewind1<'T, 'U> : Parser<'T, 'U, unit> =
        rewind 1

    /// <summary>
    /// Run a parser on a given token stream and return the result.
    /// </summary>
    /// <param name="m">The parser to run.</param>
    /// <param name="s">The token stream to run it on.</param>
    let runParser (m: Parser<'s, 'u, 'a>) (s: TokenStream<'s>) (u: 'u) =
        smindinvern.State.Lazy.runState m ((s, u), false)

    type CharParser<'u, 'a> = Parser<char, 'u, 'a>
    type StringParser<'u, 'a> = Parser<string, 'u, 'a>

    module RangeInfo =
        open System.Text
        type Position =
            {
                Line: int
                Column: int
            }
            static member inline Create(line, col) =
                { Line = line; Column = col }
        type Range =
            {
                StartPosition: Position
                EndPosition: Position
            }
            static member inline Create (start, stop) =
                { StartPosition = start; EndPosition = stop }
            static member (+) (r1: Range, r2: Range) =
                let start = min r1.StartPosition r2.StartPosition
                let stop = max r1.EndPosition r2.EndPosition
                Range.Create(start, stop)

        type Token<'T> =
            {
                Value: 'T
                Range: Range
            }
            static member inline Create (t: 'T, r: Range) =
                { Value = t; Range = r }
            static member (+) (t1: Token<'T>, t2: Token<'T>) =
                Token.Create([t1.Value; t2.Value], t1.Range + t2.Range)
            static member (+) (t1: Token<'T>, t2: Token<'T list>) =
                Token.Create(t1.Value::t2.Value, t1.Range + t2.Range)
            static member (+) (t1: Token<'T list>, t2: Token<'T>) =
                Token.Create(t1.Value @ [t2.Value], t1.Range + t2.Range)
            static member (+) (t1: Token<'T list>, t2: Token<'T list>) =
                Token.Create(t1.Value @ t2.Value, t1.Range + t2.Range)
            static member Concat (ts: Token<char list>) =
                let sb = StringBuilder()
                let sb = List.fold (fun (sb: StringBuilder) (c: char) -> sb.Append(c)) sb ts.Value
                Token.Create(sb.ToString(), ts.Range)
            static member Concat (ts: Token<char> list) =
                let (values, ranges) = List.unzip <| List.map (fun t -> (t.Value, t.Range)) ts
                let t = Token.Create(values, List.reduce (+) ranges)
                Token<_>.Concat(t)
        type TChar = Token<char>
        type TString = Token<string>

        type Parser<'s, 'u, 'a> = Types.Parser<'s*Range, 'u, 'a>
        let inline range<'T, 'U> : Parser<'T, 'U, Range> =
            snd <@> peek1
        // These definitions shadow some of those given above.
        let inline peekToken<'T, 'U> : Parser<'T, 'U, Token<'T>> =
            Token.Create <@> peek1
        let inline peek1<'T, 'U> : Parser<'T, 'U, 'T> =
            fst <@> peek1
        let inline popToken<'T, 'U> : Parser<'T, 'U, Token<'T>> =
            Token.Create <@> pop1
        let inline pop1<'T, 'U> : Parser<'T, 'U, 'T> =
            fst <@> pop1
        let inline error (message: string) : Parser<'s, 'u, 'a> =
            parse {
                let! range = range<'s, 'u>
                let s = sprintf "%s at line %i, column %i" message range.StartPosition.Line range.StartPosition.Column
                return! error s
            }
        let inline abort (msg: string) : Parser<'s, 'u, 'a> =
            parse {
                let! range = range<'s, 'u>
                let s = sprintf "%s at line %i, column %i" msg range.StartPosition.Line range.StartPosition.Column
                return! abort s
            }

        type CharParser<'u, 'a> = Parser<char, 'u, 'a>
        type StringParser<'u, 'a> = Parser<string, 'u, 'a>

open Primitives
open RangeInfo
open System.IO

type Tokenization =
    static member Tokenize(stream: 't []) : TokenStream<'t> =
        Zipper<'t>(ref stream, 0)
    static member Tokenize(stream: 't list) : TokenStream<'t> =
        Tokenization.Tokenize(Array.ofList stream)
    static member Tokenize(getter: 's -> ('s * 't option), stream: 's) : TokenStream<'t> =
        let rec tailRec (stream: 's) (ts : 't list) =
            let (stream', o) = getter stream
            match o with
                | Option.Some(t) -> tailRec stream' (t::ts)
                | Option.None -> List.rev ts
        Tokenization.Tokenize(tailRec stream [])
    static member TokenizeString(s: string) : TokenStream<char> =
        let arr = s.ToCharArray()
        Zipper<char>(ref arr, 0)
    static member TokenizeFile(sr: StreamReader) : TokenStream<char> =
        Tokenization.TokenizeString(sr.ReadToEnd())
    static member TokenizeFile(getToken: StreamReader -> 't option, fs: StreamReader) =
        Tokenization.Tokenize((fun x -> (x, getToken x)), fs)
    static member TokenizeFile(getToken: StreamReader -> 't option, fp: string) =
        using (File.OpenText(fp)) (fun sr -> Tokenization.TokenizeFile(getToken, sr))
    static member TokenizeFile(fp: string) : TokenStream<char> =
        using (File.OpenText(fp)) Tokenization.TokenizeFile

module RangeInfo =
    type private _Tokenization = Tokenization

    type Tokenization =
        static member Tokenize(stream: Token<'t> list) : TokenStream<'t * Range> =
            _Tokenization.Tokenize(List.map (fun t -> (t.Value, t.Range)) stream)
        static member TokenizeString(s: string) : TokenStream<char * Range> =
            let getter (z: Zipper<char>, range: Range) =
                match Zipper.get z with
                    | Result.Ok(c) ->
                        let start' =
                            if c = '\n' then
                                Position.Create(range.StartPosition.Line + 1, 1)
                            else
                                Position.Create(range.StartPosition.Line, range.StartPosition.Column + 1)
                        z.MoveRight(1)
                        ((z, Range.Create(start', start')), Option.Some(c, range))
                    | Result.Error(_) -> ((z, range), Option.None)
            let arr = s.ToCharArray()
            let zipper = Zipper<char>(ref arr, 0)
            let startPosition = Position.Create(1, 1)
            _Tokenization.Tokenize(getter, (zipper, Range.Create(startPosition, startPosition)))
        static member TokenizeFile(sr: StreamReader) : TokenStream<char * Range> =
            Tokenization.TokenizeString(sr.ReadToEnd())
        static member TokenizeFile(getToken: StreamReader -> ('t * int) option, fs: StreamReader) =
            _Tokenization.Tokenize((fun x -> (x, getToken x)), fs)
        static member TokenizeFile(getToken: StreamReader -> ('t * int) option, fp: string) =
            using (File.OpenText(fp)) (fun sr -> Tokenization.TokenizeFile(getToken, sr))
        static member TokenizeFile(fp: string) : TokenStream<char * Range> =
            using (File.OpenText(fp)) Tokenization.TokenizeFile
