namespace smindinvern.Parser

module Types =
    open smindinvern.Alternative
    open smindinvern.Zipper

    /// <summary>
    /// A stream of tokens.
    /// </summary>
    /// <typeparam name="'T">The type of the tokens.</typeparam>
    type TokenStream<'T> = Zipper<'T>

    /// <summary>
    /// A parser operating on a stream of tokens of type 'T, producing either
    /// a value of type 'a or a string diagnostic in case of error.  The parser
    /// also carries some state with it that may be read and/or modified throughout
    /// parsing.
    /// </summary>
    /// <typeparam name="'T">The type of the tokens.</typeparam>
    /// <typeparam name="'U">The type of the extra state available to the parser.</typeparam>
    /// <typeparam name="'a">The type of the value produced by the parser.</typeparam>
    type Parser<'T, 'U, 'a> = Alternative<TokenStream<'T> * 'U, string, 'a>
