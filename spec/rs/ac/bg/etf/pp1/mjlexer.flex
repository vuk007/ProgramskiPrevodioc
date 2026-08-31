package rs.ac.bg.etf.pp1;

import java_cup.runtime.Symbol;

%%

%column
%line
%cup

%xstate COMMENT

%{

    private Symbol new_symbol(int type) {
        return new Symbol(type, yyline + 1, yycolumn);
    }

    private Symbol new_symbol(int type, Object value) {
        return new Symbol(type, yyline + 1, yycolumn, value);
    }

%}

%init{
%init}
%eofval{
    return new_symbol(sym.EOF);
%eofval}

%%
/* =========================
   WHITESPACE
   ========================= */

" "      { }
"\b"     { }
"\t"     { }
"\r\n"   { }
"\n"     { }
"\f"     { }


/* =========================
   KEYWORDS
   ========================= */

"program"   { return new_symbol(sym.PROG); }
"break"     { return new_symbol(sym.BREAK); }
"enum"      { return new_symbol(sym.ENUM); }
("class" | "Class")     { return new_symbol(sym.CLASS); }
"abstract"  { return new_symbol(sym.ABSTRACT); }
"else"      { return new_symbol(sym.ELSE); }
"const"     { return new_symbol(sym.CONST); }
"if"        { return new_symbol(sym.IF); }
"new"       { return new_symbol(sym.NEW); }
"print"     { return new_symbol(sym.PRINT); }
"read"      { return new_symbol(sym.READ); }
"return"    { return new_symbol(sym.RETURN); }
"void"      { return new_symbol(sym.VOID); }
"extends"   { return new_symbol(sym.EXTENDS); }
"continue"  { return new_symbol(sym.CONTINUE); }
"for"       { return new_symbol(sym.FOR); }
"length"    { return new_symbol(sym.LENGTH); }
"findAny" | "findany" 	{ return new_symbol(sym.FINDANY); }
"map"     	{ return new_symbol(sym.MAP); }
"=>"      	{ return new_symbol(sym.ARROW); }
"switch"    { return new_symbol(sym.SWITCH); }
"case"      { return new_symbol(sym.CASE); }


/* =========================
   OPERATORS
   ========================= */

"=="    { return new_symbol(sym.EQ); }
"!="    { return new_symbol(sym.NEQ); }
">="    { return new_symbol(sym.GE); }
"<="    { return new_symbol(sym.LE); }
"&&"    { return new_symbol(sym.AND); }
"||"    { return new_symbol(sym.OR); }
"++"    { return new_symbol(sym.INC); }
"--"    { return new_symbol(sym.DEC); }
"+"     { return new_symbol(sym.PLUS); }
"-"     { return new_symbol(sym.MINUS); }
"*"     { return new_symbol(sym.MUL); }
"/"     { return new_symbol(sym.DIV); }
"%"     { return new_symbol(sym.MOD); }
">"     { return new_symbol(sym.GT); }
"<"     { return new_symbol(sym.LT); }
"="     { return new_symbol(sym.ASSIGN); }


/* =========================
   SEPARATORS
   ========================= */

";"     { return new_symbol(sym.SEMI); }
":"     { return new_symbol(sym.COLON); }
","     { return new_symbol(sym.COMMA); }
"."     { return new_symbol(sym.DOT); }
"("     { return new_symbol(sym.LPAREN); }
")"     { return new_symbol(sym.RPAREN); }
"["     { return new_symbol(sym.LBRACK); }
"]"     { return new_symbol(sym.RBRACK); }
"{"     { return new_symbol(sym.LBRACE); }
"}"     { return new_symbol(sym.RBRACE); }
"?"     { return new_symbol(sym.QUESTION); }


/* =========================
   BOOLEAN
   ========================= */

"true" {
    return new_symbol(sym.BOOL, 1);
}

"false" {
    return new_symbol(sym.BOOL, 0);
}

/* =========================
   IDENTIFIER
   ========================= */

[a-zA-Z][a-zA-Z0-9_]* {
    return new_symbol(sym.IDENT, yytext());
}


/* =========================
   NUMBER
   ========================= */

([1-9][0-9]*|0) {
    return new_symbol(sym.NUMBER, Integer.parseInt(yytext()));
}


/* =========================
   CHARACTER
   ========================= */

"'"."'" {
    return new_symbol(sym.CHARACTER, yytext().charAt(1));
}


/* =========================
   COMMENTS
   ========================= */

<YYINITIAL> "//" {
    yybegin(COMMENT);
}

<COMMENT> . {
}

<COMMENT> "\r\n" {
    yybegin(YYINITIAL);
}

<COMMENT> "\n" {
    yybegin(YYINITIAL);
}

/* =========================
   UNKNOWN CHARACTER
   ========================= */

. {
    System.out.println(
        "Nepoznat karakter: '" + yytext() +
        "' na liniji " + (yyline + 1) +
        ", koloni " + (yycolumn + 1)
    );
}