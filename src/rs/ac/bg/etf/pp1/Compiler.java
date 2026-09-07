package rs.ac.bg.etf.pp1;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;

import java_cup.runtime.Symbol;
import rs.ac.bg.etf.pp1.ast.SyntaxNode;
import rs.etf.pp1.mj.runtime.Code;
import rs.etf.pp1.symboltable.Tab;

public class Compiler {

	public static void main(String[] args) {
		if (args.length < 2) {
			System.err.println("Compiler <ulazni.mj> <izlazni.obj>");
			return;
		}

		String inputPath = args[0];
		String outputPath = args[1];

		try {
			Yylex microJava$Lexer = new Yylex(new BufferedReader(new FileReader(inputPath)));
			MJParser microJava$Parser = new MJParser(microJava$Lexer);
			Symbol abstract$syntax$tree = microJava$Parser.parse();
			System.out.println("Parsiranje uspesno!");
			System.out.println(abstract$syntax$tree.value.toString());

			SemanticAnalyzer microJava$semanticAnalyzer = new SemanticAnalyzer();
			Tab.init();
			((SyntaxNode)abstract$syntax$tree.value).traverseBottomUp(microJava$semanticAnalyzer);
			System.out.println("symbol table: name | addr | lvl");
			Tab.dump();

			if (microJava$semanticAnalyzer.errorDetected) {
				System.err.println("nije moguce generisati kod");
			} else {
				CodeGenerator microJava$code$generator = new CodeGenerator(
						microJava$semanticAnalyzer.getResolvedObj(),
						microJava$semanticAnalyzer.getResolvedType()
				);
				((SyntaxNode)abstract$syntax$tree.value).traverseBottomUp(microJava$code$generator);

				File obj$file = new File(outputPath);
				if (obj$file.exists()) obj$file.delete();
				Code.write(new FileOutputStream(obj$file));
			}
		} catch (Exception e) {
			System.out.println("Parsiranje neuspesno!");
			e.printStackTrace();
		}
	}
}