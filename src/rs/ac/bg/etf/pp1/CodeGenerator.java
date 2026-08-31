package rs.ac.bg.etf.pp1;

import java.time.format.ResolverStyle;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import rs.ac.bg.etf.pp1.ast.*;
import rs.etf.pp1.mj.runtime.Code;
import rs.etf.pp1.symboltable.Tab;
import rs.etf.pp1.symboltable.concepts.Obj;
import rs.etf.pp1.symboltable.concepts.Struct;

@SuppressWarnings("static-access")
public class CodeGenerator extends VisitorAdaptor{
	private Obj bool$obj = Tab.find("bool");
	private Struct bool$type = bool$obj.getType();
	
	private Struct current$type = null;
	
	private ArrayDeque<Obj> current$this = new ArrayDeque<>();
	
	private Map<SyntaxNode, Obj> obj$pointers = new HashMap<>();
	private Map<SyntaxNode, Struct> type$pointers = new HashMap<>();
	
	private ArrayDeque<Obj> designator$stack = new ArrayDeque<>();
	
	private ArrayDeque<List<Integer>> false$list$stack = new ArrayDeque<>();
	private ArrayDeque<List<Integer>> true$list$stack = new ArrayDeque<>();
	private void printDesignatorStack() {
	    for (Obj obj : designator$stack) {
	        System.out.println(obj.getName());
	    }
	    System.out.println("=======================");
	}
	
	Code code = new Code(); //sve metode i polja su staticka
							// tako da je sve jedno da li je Code ili code
							//olaksica pri pisanju koda 
	
	public CodeGenerator(Map<SyntaxNode, Obj> first, Map<SyntaxNode, Struct> second) {
		this.obj$pointers=first;
		this.type$pointers=second;
	}
	
	private void memory$indirect$read(Obj obj) {
		//memorijsko indirektno citanje 
		code.put(code.load);
		code.put(obj.getAdr());
		
	}
	private void memory$indirect$read(int adr) {
		code.put(code.load);
		code.put(adr);
	}
	
 //===============================================================
	private Obj program$obj; 
	@Override
	public void visit(ProgramName ProgramName) {
		program$obj = obj$pointers.get(ProgramName);
		for (var obj : program$obj.getLocalSymbols()) {
			if(obj.getKind() == Obj.Var) {
				obj.setAdr(code.dataSize);//globalne vrednosti dobijaju adrese
				code.dataSize++;
			}
		}
	}
	
	@Override
	public void visit(NumVal NumVal) {
		code.loadConst(NumVal.getN1());
		current$type = Tab.intType;
	}
	
	@Override
	public void visit(CharVal CharVal) {
		code.loadConst(CharVal.getC1());
		current$type = Tab.charType;
	}
	@Override
	public void visit(BoolVal BoolVal) {
		code.loadConst(BoolVal.getB1());;
		current$type = bool$type;
	}
	@Override
	public void visit(StatementPrint StatementPrint) {
		code.put(code.const_n);
		if(current$type.equals(Tab.intType)) {
			code.put(code.print);
		}
		else {
			code.put(code.bprint);
		}
	}
	
	private Struct printedType;

	@Override
	public void visit(PrintExprEnd PrintExprEnd) {
	    printedType = current$type;   // snimi PRE nego sto numConst stigne da ga prepise
	}

	@Override
	public void visit(StatementPrintWidth StatementPrintWidth) {
	    Code.put(
	    		printedType.equals(Tab.intType) 
	    		||
	    		printedType.equals(bool$type) ? 
	    				Code.print : 
	    					Code.bprint
	    					);
	}

	
	@Override
	public void visit(StatementReturn StatementReturn) {
	    Code.put(Code.exit);
	    Code.put(Code.return_);
	}

	@Override
	public void visit(StatementReturnExpr StatementReturnExpr) {
	    Code.put(Code.exit);
	    Code.put(Code.return_);
	}
	
	@Override
	public void visit(MethodName MethodName) {
	    Obj method = obj$pointers.get(MethodName);
	    method.setAdr(Code.pc);
	    if (method.getName().equals("main")) {
	        Code.mainPc = Code.pc;
	    }
	    boolean hasThis = false;
	    int localAdr = 0;
	    for (Obj o : method.getLocalSymbols()) {
	        if (o.getKind() == Obj.Var) {
	            o.setAdr(localAdr++);  
	            if (o.getName().equals("this")) {
	            	hasThis = true;
	            	current$this.add(o);
	            } 
	        }
	    }
	    
	    Code.put(Code.enter);
	    // dodaj i this u broj parametra ako postoji
	    Code.put(method.getLevel()+ (hasThis ? 1 : 0));
	    Code.put(localAdr);            	
	}
	
	// ucitavanje svih objekata po imenu
	@Override
	public void visit(DesignatorIdent DesignatorIdent) {
	    Obj obj = obj$pointers.get(DesignatorIdent);
	    if (obj.getKind() == Obj.Meth && methodNeedsThis(obj)) {
	        Code.load(current$this.pop());   // implicitni this - poziv sopstvene metode klase
	    }
	    designator$stack.push(obj);
	    printDesignatorStack();
	}
	private static final Obj LENGTH_DONE = new Obj(Obj.Con, "$len", Tab.intType);
	//operacije sa designatorima 
	@Override
	public void visit(DesignatorLength DesignatorLength) {
		 Obj base = designator$stack.pop();
		    Code.load(base);
		    Code.put(Code.dup);
		    Code.loadConst(0);

		    int first = Code.pc + 1;
		    Code.put(Code.jcc + Code.eq);
		    Code.put2(0);

		    Code.put(Code.arraylength);

		    int second = Code.pc + 1;
		    Code.put(Code.jmp);
		    Code.put2(0);

		    Code.fixup(first);
		    Code.put(Code.pop);
		    Code.loadConst(0);
		    Code.fixup(second);

		    current$type = Tab.intType;
		    designator$stack.push(LENGTH_DONE);
		
	}
	
	@Override
	public void visit(FactorDesignator FactorDesignator) {
	    Obj obj = designator$stack.pop();   
	    if (obj == LENGTH_DONE) {
	        current$type = Tab.intType;    
	    } else {
	        current$type = obj.getType();
	        Code.load(obj);
	    }
	    printDesignatorStack();
	}
	@Override
	public void visit(TermMul TermMul) {
		code.put(code.mul);
		current$type = Tab.intType; //garantovano SemAnal
	}
	@Override
	public void visit(AddExprAdd AddExprAdd) {
		code.put(code.add);
		current$type = Tab.intType; //garantovano SemAnal
	}
	@Override
	public void visit(AddExprNeg node) {
	    Code.put(Code.neg);
	}
	
	
	@Override
	public void visit(DesignatorInc DesignatorInc) {
	    Obj obj = designator$stack.pop();
	    if (obj.getKind() == Obj.Var && obj.getLevel() != 0) {
	        Code.put(Code.inc);
	        Code.put(obj.getAdr());
	        Code.put(1);                
	    } else {
	        Code.load(obj);
	        Code.loadConst(1);
	        Code.put(Code.add);
	        Code.store(obj);
	    }
	}
	
	
	@Override
	public void visit(DesignatorDec DesignatorDec) {
	    Obj obj = designator$stack.pop();
	    if (obj.getKind() == Obj.Var && obj.getLevel() != 0) {
	        Code.put(Code.inc);
	        Code.put(obj.getAdr());
	        Code.put(-1);                
	    } else {
	        Code.load(obj);
	        Code.loadConst(1);
	        Code.put(Code.sub);
	        Code.store(obj);
	    }
	}
	
	// zatvaranje metoda 
	@Override
	public void visit(MethodDeclVars methodDeclVars) { visit((MethodDecl) methodDeclVars); }
	@Override
	public void visit(MethodDeclNoVars MethodDeclNoVars) { visit((MethodDecl) MethodDeclNoVars); }
	@Override
	public void visit(MethodDeclNoParameter MethodDeclNoParameter) { visit((MethodDecl) MethodDeclNoParameter); }
	@Override
	public void visit(MethodDeclNoVarsNoParameter MethodDeclNoVarsNoParameter) { visit((MethodDecl) MethodDeclNoVarsNoParameter); }
	@Override
	public void visit(MethodDecl MethodDecl) {
	    Code.put(Code.exit);
	    Code.put(Code.return_);
	}
	
	// dodela vrednosti 
	@Override
	public void visit(DesignatorAssign DesignatorAssign) {
		Obj obj = designator$stack.pop();
		code.store(obj);
	}
	
	// POZIVI METODA
	private void generateCall(Obj method) {
	    Code.put(Code.call);
	    Code.put2(method.getAdr() - Code.pc + 1);   // sirina 2 polja za adr 
	}

	@Override
	public void visit(FactorCallPars printDesignatorStack) { generateCall(designator$stack.pop()); }
	@Override
	public void visit(FactorCallNoPars FactorCallNoPars) { generateCall(designator$stack.pop()); }
	@Override
	public void visit(DesignatorCallPars node) {
	    Obj meth = designator$stack.pop();
	    generateCall(meth);
	    if (!meth.getType().equals(Tab.noType)) Code.put(Code.pop); // povratna vrednost
	}
	@Override
	public void visit(DesignatorCallNoPars FactorCallNoPars) {
	    Obj meth = designator$stack.pop();
	    generateCall(meth);
	    if (!meth.getType().equals(Tab.noType)) Code.put(Code.pop); // povratna vrednost
	}
	
	// Citanje sa standardnog ulaza
	@Override
	public void visit(StatementRead StatementRead) {
	    Obj obj = designator$stack.pop();
	    if (obj.getType().equals(Tab.charType)) {
	        Code.put(Code.bread);
	    } else {
	        Code.put(Code.read);
	    }
	    code.store(obj);
	}
	
	//relacione operacije (uslovi) 
	private relop current$rel$op = null;
	enum relop {EQ , NEQ , LE , LT , GT ,GE}
	@Override
	public void visit(CondFactRel CondFactRel) {
		jmp$fix$adrr.push(code.pc+1);
		switch (current$rel$op) {
		case EQ: {
			code.putFalseJump(code.eq, 0);
			break;
		}
		case NEQ:
		{
			code.putFalseJump(code.eq, 0);
			break;
		}
		case LE:
		{
			code.putFalseJump(code.le,0);
			break;
		}
		case LT:
		{
			code.putFalseJump(code.lt,0);
			break;
		}
		case GT:
		{
			code.putFalseJump(code.gt,0);
			break;
		}
		case GE:
		{
			code.putFalseJump(code.ge,0);
			break;
		}
		default:
			throw new IllegalArgumentException("Unexpected value: " + current$rel$op);
		}
		current$rel$op = null;
	}
	
	@Override
	public void visit(CondFactExpr CondFactExpr) {
	    Code.loadConst(0);
	    jmp$fix$adrr.push(Code.pc + 1);
	    Code.putFalseJump(Code.ne, 0);   
	}
	
	@Override
	public void visit(RelopEQ RelopEQ) {
		current$rel$op = relop.EQ;
	}
	@Override
	public void visit(RelopNEQ relopNEQ) {
		current$rel$op = relop.NEQ;
	}
	@Override
	public void visit(RelopLE RelopLE) {
		current$rel$op = relop.LE;
	}
	@Override
	public void visit(RelopLT RelopLT) {
		current$rel$op = relop.LT;
	}
	@Override
	public void visit(RelopGT RelopGT ) {
		current$rel$op = relop.GT;
	}
	@Override
	public void visit(RelopGE RelopGE) {
		current$rel$op = relop.GE;
	}
	
	@Override
	public void visit(StatementIf StatementIf) {
		var val = jmp$fix$adrr.pop().intValue(); 
		code.fixup(val);
	}
	
	@Override
	public void visit(StatementIfElse StatementIfElse) {
		var val = jmp$fix$adrr.pop().intValue(); 
		code.fixup(val);
	}
	
	@Override
	public void visit(ElseJmp ElseJmp) {
		var val = jmp$fix$adrr.pop().intValue(); 
		code.putJump(0);
		code.fixup(val);
		jmp$fix$adrr.push(code.pc+1);
	}
	
	
	// FOR STATEMENT
	private ArrayDeque<List<Integer>> break$stack = new ArrayDeque<>();
	private ArrayDeque<Integer> continue$target$stack = new ArrayDeque<>();
	// za break i continue 
	
	private ArrayDeque<Integer> for$cond$start = new ArrayDeque<>();
	private ArrayDeque<Integer> for$over$start = new ArrayDeque<>();
	private ArrayDeque<Boolean> for$has$cond = new ArrayDeque<>();
	private int for$phase = 0;   // 0=ocekuje init, 1=ocekuje uslov, 2=ocekuje inkrement

	private void forHeaderCycle() {
	    if (for$phase == 0) {
	        for$cond$start.push(Code.pc);
	        for$phase = 1;
	    } else if (for$phase == 1) {
	    	jmp$fix$adrr.push(code.pc+1);
	        Code.putJump(0);  
	        for$over$start.push(Code.pc );  
	        for$phase = 2;
	    } else {
	        for$phase = 0;
	    }
	}

	@Override
	public void visit(OptDesignatorStatementSome node) { forHeaderCycle(); }
	@Override
	public void visit(OptDesignatorStatementNone node) { forHeaderCycle(); }

	@Override
	public void visit(OptConditionSome OptConditionSome) {
	    for$has$cond.push(true);
	    forHeaderCycle();
	}
	@Override
	public void visit(OptConditionNone OptConditionNone) {
	    for$has$cond.push(false);
	    forHeaderCycle();
	}

	@Override
	public void visit(ForHeader ForHeader) {
	    int condAdr = for$cond$start.pop();
	    Code.putJump(condAdr);                         	
	    Code.fixup(jmp$fix$adrr.pop()); 
	    
	    break$stack.push(new ArrayList<>());
	    continue$target$stack.push(for$over$start.peek());   
	}

	@Override
	public void visit(StatementFor StatementFor) {
	    boolean hadCond = for$has$cond.pop();
	    int overStart = for$over$start.pop();
	    Code.putJump(overStart);          
	    if (hadCond) {
	        Code.fixup(jmp$fix$adrr.pop()); 
	    }
	    continue$target$stack.pop();
	    for (int patchAdr : break$stack.pop()) {
	        Code.fixup(patchAdr);
	    }
	}
	
	@Override
	public void visit(StatementBreak StatementBreak) {
	    break$stack.peek().add(Code.pc + 1);  
	    Code.putJump(0);                        
	}

	@Override
	public void visit(StatementContinue StatementContinue) {
	    Code.putJump(continue$target$stack.peek());  
	}
	
	//Stvaranje niza i pristup elementima niza 
	
	@Override
	public void visit(FactorNewArray FactorNewArray) {
		current$type = type$pointers.get(FactorNewArray);   
	    Code.put(Code.newarray);
	    if (current$type.equals(Tab.charType)) {
	        Code.put(0);
	    } else {
	        Code.put(1);
	    }
	}
	
	@Override
	public void visit(DesignatorArrayElem DesignatorArrayElem) {
		Obj obj = designator$stack.pop();
		memory$indirect$read(obj.getAdr());
		
		//zamena mesta//
			code.put(code.dup_x1);
			code.put(code.pop);
		//
		
		Obj elem = new Obj(Obj.Elem, obj.getName(), obj.getType().getElemType());
	    designator$stack.push(elem);
	}
	
	
	//klase, pristup poljima klase i deklaracija klase 
	
	@Override
	public void visit(FactorNewObj FactorNewObj) {
		var struct = type$pointers.get(FactorNewObj);
		code.put(code.new_);
		code.put2(struct.getNumberOfFields() * 4);
	}
	
	@Override
	public void visit(DesignatorField DesignatorField) {
		//zamena objekta jer vec sam code.load(...)
		// u odnosu na kind u designator assign
	    Obj field = obj$pointers.get(DesignatorField);
	    Obj instance = designator$stack.pop();
	    if (instance.getKind() != Obj.Type) {   // preskoci load ako je baza samo ime tipa (enum)
	        code.load(instance);
	    }
	    designator$stack.push(field);
	}
	
	// za ubacivanje fake this ako je potrebno 
	private boolean methodNeedsThis(Obj meth) {
	    Iterator<Obj> it = meth.getLocalSymbols().iterator();
	    return it.hasNext() && it.next().getName().equals("this");
	}
}
