namespace smindinvern.Parser

module Monad =

    let inject = smindinvern.Alternative.Monad.inject
    let bind = smindinvern.Alternative.Monad.bind
    let (>>=) = smindinvern.Alternative.Monad.(>>=)

    let parse = smindinvern.Alternative.Monad.alt

    let (<@>) = smindinvern.Alternative.Monad.(<@>)
    let (<*>) = smindinvern.Alternative.Monad.(<*>)
    let sequence = smindinvern.Alternative.Monad.sequence


