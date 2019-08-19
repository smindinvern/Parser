namespace smindinvern.Parser

module Types =
    open Zipper

    /// <summary>
    /// A stream of tokens.
    /// <typeparam name="'T">The type of the tokens.</typeparam>
    /// </summary>
    type TokenStream<'T> = Zipper<'T>

    /// <summary>
    /// A parser operating on a stream of tokens of type 'T, producing either
    /// a value of type 'a or a string diagnostic in case of error.  The parser
    /// also carries some state with it that may be read and/or modified throughout
    /// parsing.
    /// <typeparam name="'T">The type of the tokens.</typeparam>
    /// <typeparam name="'U">The type of the extra state available to the parser.</typeparam>
    /// <typeparam name="'a">The type of the value produced by the parser.</typeparam>
    /// </summary>
    type Parser<'T, 'U, 'a> = State.State<TokenStream<'T> * 'U * bool, Result<'a, string>>
