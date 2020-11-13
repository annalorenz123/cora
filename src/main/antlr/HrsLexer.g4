/**************************************************************************************************
 Copyright 2020 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

/**
 * This is a lexer for files in the standard human-readable format of the termination or confluence
 * competitions, limited to higher-order TRSs (.hrs files).
 */
lexer grammar HrsLexer;

@header {
package cora.parsers;
}

/* Lexer */

WHITESPACE          : [ \t\r\n]+ -> skip ;

ARROW               : '-' '>' ;

COMMA               : ',' ;

// identifiers may not contain ->, which we handle using lookaheads
IDENTIFIER          : ( (~ ([ \t\n\r\\():"|.,-]) ) |
                        ('-' {_input.LA(1) != '>'}?)
                      )+ ;

DECLARE             : ':';

LAMBDA              : '\\';

DOT                 : '.';

BRACKETOPEN         : '(' ;

BRACKETCLOSE        : ')' ;

VARSDECSTART        : '(' 'V' 'A' 'R' ;

FUNSDECSTART        : '(' 'F' 'U' 'N' ;

RULESDECSTART       : '(' 'R' 'U' 'L' 'E' 'S' ;

COMMENT             : '(' 'C' 'O' 'M' 'M' 'E' 'N' 'T' .* ')' -> skip;

