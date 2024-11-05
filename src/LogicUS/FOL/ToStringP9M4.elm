module LogicUS.FOL.ToStringP9M4 exposing (ffol2P9M4Str, ffol2P9M4Str2, sfol2P9M4Str, sfol2P9M4Str2, ffol2P9M4StrUnsafe, sfol2P9M4StrUnsafe)

import Tuple exposing (first)
import LogicUS.FOL.SyntaxSemantics exposing (FormulaFOL(..))
import Dict exposing (Dict)
import LogicUS.FOL.SyntaxSemantics exposing (SetFOL)
import LogicUS.FOL.SyntaxSemantics exposing (Variable)
import LogicUS.FOL.SyntaxSemantics exposing (Ident)
import LogicUS.FOL.SyntaxSemantics exposing (Term(..))

ffol2P9M4Str : FormulaFOL -> String
ffol2P9M4Str f =
    (first <| ffol2P9M4Str2 f {vi = 0, vdic = Dict.empty, ci = 0, cdic = Dict.empty, fi = 0, fdic = Dict.empty, pi = 0, pdic = Dict.empty}) ++ "."


sfol2P9M4Str : SetFOL -> String
sfol2P9M4Str fs =
    Tuple.first <| sfol2P9M4Str2 fs {vi = 0, vdic = Dict.empty, ci = 0, cdic = Dict.empty, fi = 0, fdic = Dict.empty, pi = 0, pdic = Dict.empty}



sfol2P9M4Str2 : List FormulaFOL -> { vi : Int, vdic : Dict Variable Int, pi : Int, pdic : Dict Ident Int, fi : Int, fdic : Dict Ident Int, ci : Int, cdic : Dict Ident Int } -> ( String, { vi : Int, vdic : Dict Variable Int, pi : Int, pdic : Dict Ident Int, fi : Int, fdic : Dict Ident Int, ci : Int, cdic : Dict Ident Int } )
sfol2P9M4Str2 fs ini =
     List.foldl 
        (\f (res, info) -> Tuple.mapFirst (\ s -> res ++ s ++ ".\n") <| ffol2P9M4Str2 f {info | vi = 0, vdic = Dict.empty})
        ("", ini)
        fs

ffol2P9M4Str2 : 
    FormulaFOL 
    -> { vi : Int, vdic : Dict Variable Int, pi : Int, pdic : Dict Ident Int, fi : Int, fdic : Dict Ident Int, ci: Int, cdic : Dict Ident Int }
    -> ( String,  { vi : Int, vdic : Dict Variable Int, pi : Int, pdic : Dict Ident Int, fi : Int, fdic : Dict Ident Int, ci: Int, cdic : Dict Ident Int })
ffol2P9M4Str2 f info =
    case f of
        Pred p [] ->
            case Dict.get p info.pdic of
                Just i -> 
                    ("P" ++ (String.fromInt i), info)

                Nothing ->
                    ("P" ++ (String.fromInt info.pi), {info | pi = (info.pi + 1), pdic = Dict.insert p info.pi info.pdic})

        Pred p ts -> 
            case Dict.get p info.pdic of
                Just i -> 
                    let
                        (tstr, ninfo) = terms2P9M4Str ts info
                    in
                    ("P" ++ (String.fromInt i) ++ "(" ++ tstr ++ ")", ninfo)

                Nothing -> 
                    let
                        info_ = {info | pi = (info.pi + 1), pdic = Dict.insert p info.pi info.pdic}
                    in
                    let
                        (tstr, ninfo) = terms2P9M4Str ts info_
                    in
                    ("P" ++ (String.fromInt info.pi) ++ "(" ++ tstr ++ ")", ninfo)

        Equal t1 t2 ->
            let
                (t1str, info1) = term2P9M4Str t1 info
            in
            let
                (t2str, info2) = term2P9M4Str t2 info1
            in
            ("(" ++ t1str ++ " = " ++ t2str ++ ")", info2)

        Neg (Equal t1 t2) ->
            let
                (t1str, info1) = term2P9M4Str t1 info
            in
            let
                (t2str, info2) = term2P9M4Str t2 info1
            in
            ("(" ++ t1str ++ " != " ++ t2str ++ ")", info2)

        Neg f1 ->
            let
                (f1str, info1) = ffol2P9M4Str2 f1 info
            in
            ("-" ++ f1str, info1)
            

        Conj f1 f2 ->
            let
                (f1str, info1) = ffol2P9M4Str2 f1 info
            in
            let
                (f2str, info2) = ffol2P9M4Str2 f2 info1
            in
            ("(" ++ f1str ++ " & " ++ f2str ++ ")", info2)

        Disj f1 f2 ->
            let
                (f1str, info1) = ffol2P9M4Str2 f1 info
            in
            let
                (f2str, info2) = ffol2P9M4Str2 f2 info1
            in
            ("(" ++ f1str ++ " | " ++ f2str ++ ")", info2)
        
        Impl f1 f2 ->
            let
                (f1str, info1) = ffol2P9M4Str2 f1 info
            in
            let
                (f2str, info2) = ffol2P9M4Str2 f2 info1
            in
            ("(" ++ f1str ++ " -> " ++ f2str ++ ")", info2)

        Equi f1 f2 ->
            let
                (f1str, info1) = ffol2P9M4Str2 f1 info
            in
            let
                (f2str, info2) = ffol2P9M4Str2 f2 info1
            in
            ("(" ++ f1str ++ " <-> " ++ f2str ++ ")", info2)
        
        Exists v f1 ->
            let
                (vstr, info1) = (varIdxP9M4Str info.vi, {info | vi = (info.vi + 1), vdic = Dict.insert v info.vi info.vdic})
            in
            let
                (f1str, info2) = ffol2P9M4Str2 f1 info1
            in
            
            ("exists " ++ vstr ++ " " ++ f1str, info2)

        Forall v f1 ->
            let
                (vstr, info1) = (varIdxP9M4Str info.vi, {info | vi = (info.vi + 1), vdic = Dict.insert v info.vi info.vdic})
            in
            let
                (f1str, info2) = ffol2P9M4Str2 f1 info1
            in
            
            ("all " ++ vstr ++ " " ++ f1str, info2)


        Taut -> ("$T", info)

        Insat -> ("$F", info)


ffol2P9M4StrUnsafe : FormulaFOL -> String
ffol2P9M4StrUnsafe f =
    (first <| ffol2P9M4StrUnsafe2 f (0, Dict.empty)) ++ "."

sfol2P9M4StrUnsafe : SetFOL -> String
sfol2P9M4StrUnsafe fs =
    String.join "\n" <| List.map ffol2P9M4StrUnsafe fs

ffol2P9M4StrUnsafe2 : 
    FormulaFOL 
    -> (Int, Dict Variable Int)
    -> ( String, (Int, Dict Variable Int))
ffol2P9M4StrUnsafe2 f vinfo =
    let
        indices2Str xs = 
            case xs of
                [] -> ""
                _ -> "_" ++ (String.join "." <| List.map String.fromInt xs)
    in
    case f of
        Pred (p, sub) [] ->
            ("\"" ++ p ++ indices2Str sub  ++ "\"", vinfo)

        Pred (p, sub) ts -> 
            let
                 (tstr, nvinfo) = terms2P9M4StrUnsafe ts vinfo

            in
                ("\"" ++ p ++  indices2Str sub  ++ "\"(" ++ tstr++ ")", nvinfo)

        Equal t1 t2 ->
            let
                (tstr1, nvinfo) = term2P9M4StrUnsafe t1 vinfo
                (tstr2, nvinfo2) = term2P9M4StrUnsafe t2 nvinfo
            in
            ("(" ++ tstr1 ++ " = " ++ tstr2 ++ ")", nvinfo2)

        Neg (Equal t1 t2) ->
            let
                (tstr1, nvinfo) = term2P9M4StrUnsafe t1 vinfo
                (tstr2, nvinfo2) = term2P9M4StrUnsafe t2 nvinfo
            in
            ("(" ++ tstr1 ++ " != " ++ tstr2 ++ ")", nvinfo2)  

        Neg f1 ->
            let
                (f1str, info1) = ffol2P9M4StrUnsafe2 f1 vinfo
            in
            ("-" ++  f1str, info1)
            

        Conj f1 f2 ->
            let
                (f1str, info1) = ffol2P9M4StrUnsafe2 f1 vinfo
            in
            let
                (f2str, info2) = ffol2P9M4StrUnsafe2 f2 info1
            in
            ("(" ++ f1str ++ " & " ++ f2str ++ ")", info2)

        Disj f1 f2 ->
            let
                (f1str, info1) = ffol2P9M4StrUnsafe2 f1 vinfo
            in
            let
                (f2str, info2) = ffol2P9M4StrUnsafe2 f2 info1
            in
            ("(" ++ f1str ++ " | " ++ f2str ++ ")", info2)
        
        Impl f1 f2 ->
            let
                (f1str, info1) = ffol2P9M4StrUnsafe2 f1 vinfo
            in
            let
                (f2str, info2) = ffol2P9M4StrUnsafe2 f2 info1
            in
            ("(" ++ f1str ++ " -> " ++ f2str ++ ")", info2)

        Equi f1 f2 ->
            let
                (f1str, info1) = ffol2P9M4StrUnsafe2 f1 vinfo
            in
            let
                (f2str, info2) = ffol2P9M4StrUnsafe2 f2 info1
            in
            ("(" ++ f1str ++ " <-> " ++ f2str ++ ")", info2)
        
        Exists v f1 ->
            let
                (i,vdic) = vinfo
            in
            
            let
                (vstr, info1) = (varIdxP9M4Str i, (i+1, Dict.insert v i vdic))
            in
            let
                (f1str, info2) = ffol2P9M4StrUnsafe2 f1 info1
            in
            
            ("exists " ++ vstr ++ " " ++ f1str, info2)

        Forall v f1 ->
            let
                (i,vdic) = vinfo
            in
            
            let
                (vstr, info1) = (varIdxP9M4Str i, (i+1, Dict.insert v i vdic))
            in
            let
                (f1str, info2) = ffol2P9M4StrUnsafe2 f1 info1
            in
            
            ("all " ++ vstr ++ " " ++ f1str, info2)


        Taut -> ("$T", vinfo)

        Insat -> ("$F", vinfo)

terms2P9M4Str : List Term -> { vi : Int, vdic : Dict Variable Int, pi : Int, pdic : Dict Ident Int, fi : Int, fdic : Dict Ident Int, ci: Int, cdic : Dict Ident Int } 
    -> ( String,  { vi : Int, vdic : Dict Variable Int, pi : Int, pdic : Dict Ident Int, fi : Int, fdic : Dict Ident Int, ci: Int, cdic : Dict Ident Int }) 

terms2P9M4Str ts info =
    case ts of
        [] -> ("", info)
        x::xs -> 
            List.foldl (\xi (s_, info_) ->  (\(si, infoi) -> (s_ ++ "," ++ si, infoi) ) (term2P9M4Str xi info_) ) (term2P9M4Str x info) xs

term2P9M4Str : 
    Term -> { vi : Int, vdic : Dict Variable Int, pi : Int, pdic : Dict Ident Int, fi : Int, fdic : Dict Ident Int, ci: Int, cdic : Dict Ident Int } 
    -> ( String,  { vi : Int, vdic : Dict Variable Int, pi : Int, pdic : Dict Ident Int, fi : Int, fdic : Dict Ident Int, ci: Int, cdic : Dict Ident Int }) 
term2P9M4Str t info =
    case t of
        Var v ->
            case Dict.get v info.vdic of
                Just i -> (varIdxP9M4Str i, info)

                Nothing -> (varIdxP9M4Str info.vi, {info | vi = (info.vi + 1), vdic = Dict.insert v info.vi info.vdic})

        Func c [] ->
            case Dict.get c info.cdic of
                Just i ->  ("c" ++ (String.fromInt i), info)
                Nothing -> ("c" ++ (String.fromInt info.ci), {info | ci = (info.ci + 1), cdic = Dict.insert c info.ci info.cdic})

        Func f ts ->
            case Dict.get f info.fdic of
                Just i -> 
                    let
                        (tstr, ninfo) = terms2P9M4Str ts info
                    in
                    ("f" ++ (String.fromInt i) ++ "(" ++ tstr ++ ")", ninfo)
                
                Nothing -> 
                    let
                        info_ = {info | fi = (info.fi + 1), fdic = Dict.insert f info.fi info.fdic}
                    in
                    let
                        (tstr, ninfo) = terms2P9M4Str ts info_
                    in
                    ("f" ++ (String.fromInt info.fi) ++ "(" ++ tstr ++ ")", ninfo)
varIdxP9M4Str : Int -> String
varIdxP9M4Str i =
    case i of
        0 -> "A"
        1 -> "B"
        2 -> "C"
        3 -> "D"
        4 -> "E"
        _ -> "V" ++ String.fromInt (i+1)


term2P9M4StrUnsafe : Term -> (Int, Dict Variable Int)  -> (String, (Int,  Dict Variable Int))
term2P9M4StrUnsafe t (i, vdic)=
    let
        indices2Str xs =
            case xs of
                [] -> ""
                _ -> "_" ++ (String.join "." <| List.map String.fromInt xs)

    in
    
    case t of
        Var v ->
            case Dict.get v vdic of
                Just x -> (varIdxP9M4Str x, (i,vdic))

                Nothing -> (varIdxP9M4Str i, (i+1, Dict.insert v i vdic))

        Func (c, sub) [] ->
            ("\"" ++ c ++ indices2Str sub  ++ "\"", (i, vdic))

        Func (f, sub) ts ->
            let
                 (tstr, vinfo) = terms2P9M4StrUnsafe ts (i,vdic)

            in
                ("\"" ++ f ++ indices2Str sub  ++ "\"(" ++ tstr++ ")", vinfo)

terms2P9M4StrUnsafe : List Term -> ( Int, Dict Variable Int ) -> (String, (Int,  Dict Variable Int))
terms2P9M4StrUnsafe ts vinfo =
    case ts of
        [] -> ("", vinfo)
        x::xs -> 
            List.foldl (\xi (s_, info_) ->  (\(si, infoi) -> (s_ ++ "," ++ si, infoi) ) (term2P9M4StrUnsafe xi info_) ) (term2P9M4StrUnsafe x vinfo) xs