package rs.ac.bg.etf.pp1;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.Reader;


import java_cup.runtime.Symbol;

public class LexerTest {

	private static String getTokenName(int token) {
	    try {
	        for (var field : sym.class.getFields()) {
	            if (field.getType() == int.class && field.getInt(null) == token) {
	                return field.getName();
	            }
	        }
	    } catch (Exception e) {
	        e.printStackTrace();
	    }

	    return "UNKNOWN";
	}
	
    public static void main(String[] args) {

        try {
            Reader r = new BufferedReader(new FileReader("test.txt"));

            Yylex y = new Yylex(r);
            System.out.println("POCETAK \n");
            int i = 0; 
            Symbol s;
	        do {
	            s = y.next_token();
	            
	            System.out.println(
	                "TOKEN: " + s.sym + "(" + getTokenName(s.sym) + ")" +
	                " | line: " + (s.left) +
	                " | col: " + (s.right) +
	                " | val: " + s.value
	            );
	        } while (s.sym != sym.EOF);
            System.out.println("KRAJ");
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}