package rs.ac.bg.etf.pp1;

import java.io.BufferedReader;
import java.io.FileReader;

import java_cup.runtime.Symbol;
import rs.ac.bg.etf.pp1.ast.Program;

public class ParserTest {
	public static void main(String[] args) {
		try {			
			Yylex microJava$Lexer = new Yylex(new BufferedReader(new FileReader("test.txt")));
			MJParser microJava$Parser = new MJParser(microJava$Lexer);
			Symbol abstract$syntax$tree = microJava$Parser.parse();
			System.out.println("Parsiranje uspesno!");
			System.out.println(abstract$syntax$tree.value.toString());			
		}catch (Exception e) {
			System.out.println("Parsiranje neuspesno!");
			e.printStackTrace();
		}
	}
}
