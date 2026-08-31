package rs.ac.bg.etf.pp1;


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
	
	private Obj current$this = null;
	
	private ArrayDeque<Obj> callBase$stack = new ArrayDeque<>();
	
	
	private Map<Struct, Integer> vtable$adr= new HashMap<>();
	private Map<SyntaxNode, Obj> obj$pointers = new HashMap<>();
	private Map<SyntaxNode, Struct> type$pointers = new HashMap<>();
	
	private ArrayDeque<Obj> designator$stack = new ArrayDeque<>();
	private ArrayDeque<Integer> jmp$fix$adrr = new ArrayDeque<>();
	
	private ArrayDeque<List<Integer>> false$list$stack = new ArrayDeque<>();
	// lista listi za popunjavanje skoka 
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
	    if (current$type.equals(Tab.intType) || current$type.equals(bool$type)) {
	        code.put(code.print);
	    } else {
	        code.put(code.bprint);
	    }
	}
	
	private Struct printedType;

	@Override
	public void visit(PrintExprEnd PrintExprEnd) {
	    printedType = current$type;  
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
		// void return 
	    Code.put(Code.exit);
	    Code.put(Code.return_);
	}

	@Override
	public void visit(StatementReturnExpr StatementReturnExpr) {
		// isto totalno kao return 
	    Code.put(Code.exit);
	    Code.put(Code.return_);
	}
	
	private void emitVtableSetup() {
	    for (Map.Entry<Struct, Integer> entry : vtable$adr.entrySet()) {
	        Struct classType = entry.getKey();
	        int addr = entry.getValue();
	        for (Obj member : classType.getMembers()) {
	            if (member.getKind() != Obj.Meth) continue;
	            String name = member.getName();
	            for (int i = 0; i < name.length(); i++) {
	                Code.loadConst(name.charAt(i));
	                Code.put(Code.putstatic);
	                Code.put2(addr++);
	            }
	            Code.loadConst(-1);
	            Code.put(Code.putstatic);
	            Code.put2(addr++);

	            Code.loadConst(member.getAdr());
	            Code.put(Code.putstatic);
	            Code.put2(addr++);
	        }
	        Code.loadConst(-2);
	        Code.put(Code.putstatic);
	        Code.put2(addr++);
	    }
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
	                current$this = o;
	            }
	        }
	    }

	    Code.put(Code.enter);
	    Code.put(method.getLevel() + (hasThis ? 1 : 0));
	    Code.put(localAdr);

	    if (method.getName().equals("main")) {   
	        emitVtableSetup();
	    }
	}
	
	// ucitavanje svih objekata po imenu
	@Override
	public void visit(DesignatorIdent DesignatorIdent) {
	    Obj obj = obj$pointers.get(DesignatorIdent);
	    if (obj.getKind() == Obj.Fld) {
	        Code.load(current$this);  
	    } else if (obj.getKind() == Obj.Meth && methodNeedsThis(obj)) {
	        Code.load(current$this);
	        callBase$stack.push(current$this);
	    }
	    designator$stack.push(obj);
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
	}
	
	//ARITMETICKE OPERACIJE 
	
	private enum arith { ADD, SUB, MUL, DIV, MOD }
	private arith current$add$op;
	private arith current$mul$op;
	
	@Override
	public void visit(AddopADD AddopADD) { current$add$op = arith.ADD; }
	@Override
	public void visit(AddopMIN AddopMIN) { current$add$op = arith.SUB; }
	@Override
	public void visit(MulopMUL MulopMUL) { current$mul$op = arith.MUL; }
	@Override
	public void visit(MulopDIV MulopDIV) { current$mul$op = arith.DIV; }
	@Override
	public void visit(MulopMOD MulopMOD) { current$mul$op = arith.MOD; }
	
	@Override
	public void visit(TermMul TermMul) {
		// izvrsava se pre sabiranja tako da je 
		//osigurana leva asocijativnost 
	    switch (current$mul$op) {
	        case DIV: Code.put(Code.div); break;
	        case MOD: Code.put(Code.rem); break;
	        default: Code.put(Code.mul); break;
	    }
	    current$type = Tab.intType;
	}
	@Override
	public void visit(AddExprAdd AddExprAdd) {
	    Code.put(current$add$op == arith.SUB ? Code.sub : Code.add);
	    current$type = Tab.intType;
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
	    current$this = null;   // reset za sledecu metodu
	}
	
	// dodela vrednosti 
	@Override
	public void visit(DesignatorAssign DesignatorAssign) {
		Obj obj = designator$stack.pop();
		code.store(obj);
	}
	
	// POZIVI METODA
	private void generateCall(Obj method) {
	    if (methodNeedsThis(method)) {
	        Obj base = callBase$stack.pop();
	        Code.load(base);
	        Code.put(Code.getfield);
	        Code.put2(0);
	        emitInvokevirtual(method.getName());
	    } else {
	        Code.put(Code.call);
	        Code.put2(method.getAdr() - Code.pc + 1);
	    }
	}
	
	private void emitInvokevirtual(String name) {
	    Code.put(Code.invokevirtual);
	    for (int i = 0; i < name.length(); i++) {
	        Code.put4(name.charAt(i));
	    }
	    Code.put4(-1);
	}

	@Override
	public void visit(FactorCallPars printDesignatorStack) {
		 Obj method = designator$stack.pop();
		 generateCall(method);
		 current$type = method.getType();
	}
	@Override
	public void visit(FactorCallNoPars FactorCallNoPars) {
		 	Obj method = designator$stack.pop();
		    generateCall(method);
		    current$type = method.getType();
		}
	@Override
	public void visit(DesignatorCallPars node) {
	    Obj meth = designator$stack.pop();
	    generateCall(meth);
	    if (!meth.getType().equals(Tab.noType)) Code.put(Code.pop); // povratna vrednost
	}		// skida ako je void
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
	    List<Integer> f = new ArrayList<>();
	    f.add(Code.pc + 1);
	    switch (current$rel$op) {
	        case EQ: Code.putFalseJump(Code.eq, 0); break;
	        case NEQ: Code.putFalseJump(Code.ne, 0); break;
	        case LE: Code.putFalseJump(Code.le, 0); break;
	        case LT: Code.putFalseJump(Code.lt, 0); break;
	        case GT: Code.putFalseJump(Code.gt, 0); break;
	        case GE: Code.putFalseJump(Code.ge, 0); break;
	    }
	    current$rel$op = null;
	    false$list$stack.push(f);
	    true$list$stack.push(new ArrayList<>());  
	}
	
	@Override
	public void visit(CondFactExpr CondFactExpr) {
	    Code.loadConst(0);
	    List<Integer> f = new ArrayList<>();
	    f.add(Code.pc + 1);
	    Code.putFalseJump(Code.ne, 0);
	    false$list$stack.push(f);
	    true$list$stack.push(new ArrayList<>());
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
	public void visit(CondTermAnd CondTermAnd) {
		//zamena mesta levog i desnog stacka jer levi ispada 
		// ova zamena se radi do CONDFACT kad stigne on je poslednji 
	    List<Integer> rightFalse = false$list$stack.pop();
	    List<Integer> rightTrue = true$list$stack.pop();
	    List<Integer> leftFalse = false$list$stack.pop();
	    List<Integer> leftTrue = true$list$stack.pop();

	    leftFalse.addAll(rightFalse);
	    leftTrue.addAll(rightTrue);

	    false$list$stack.push(leftFalse);
	    true$list$stack.push(leftTrue);
	    
	}
	
	private ArrayDeque<List<Integer>> pendingOrTrue$stack = new ArrayDeque<>();

	@Override
	public void visit(OrMarker OrMarker) {
	    List<Integer> leftFalse = false$list$stack.pop();
	    List<Integer> leftTrue = true$list$stack.pop();

	    List<Integer> jumpToTrue = new ArrayList<>();
	    jumpToTrue.add(Code.pc + 1);
	    Code.putJump(0);   // ako je levo tacno, preskoci desni operand

	    for (int adr : leftFalse) Code.fixup(adr);   // ako je levo netacno, PADNI OVDE i probaj desno

	    leftTrue.addAll(jumpToTrue);
	    pendingOrTrue$stack.push(leftTrue);
	}

	@Override
	public void visit(ConditionOr ConditionOr) {
		//isti princip kao kod AND 
	    List<Integer> rightFalse = false$list$stack.pop();
	    List<Integer> rightTrue = true$list$stack.pop();
	    List<Integer> leftTrue = pendingOrTrue$stack.pop();

	    leftTrue.addAll(rightTrue);

	    false$list$stack.push(rightFalse);
	    true$list$stack.push(leftTrue);
	}
	
	private ArrayDeque<List<Integer>> pendingIfFalse$stack = new ArrayDeque<>();
	

	@Override
	public void visit(IfCond IfCond) {
	    List<Integer> falseList = false$list$stack.pop();
	    List<Integer> trueList = true$list$stack.pop();
	    for (int adr : trueList) Code.fixup(adr);   // patch SADA - tacno pocetak then-grane
	    pendingIfFalse$stack.push(falseList);        // false ostaje za kasnije (kao i pre)
	}
	@Override
	public void visit(StatementIf StatementIf) {
	    for (int adr : pendingIfFalse$stack.pop()) Code.fixup(adr);
	}
	
	@Override
	public void visit(StatementIfElse StatementIfElse) {
	    for (int adr : pendingIfFalse$stack.pop()) Code.fixup(adr);
	}
	@Override
	public void visit(ElseJmp ElseJmp) {
	    List<Integer> falseList = pendingIfFalse$stack.pop();
	    List<Integer> skipElse = new ArrayList<>();
	    skipElse.add(Code.pc + 1);
	    Code.putJump(0);
	    for (int adr : falseList) Code.fixup(adr);
	    List<Integer> wrapped = new ArrayList<>();
	    wrapped.add(skipElse.get(0));
	    pendingIfFalse$stack.push(wrapped);
	}

	
	// FOR STATEMENT
	private ArrayDeque<List<Integer>> break$stack = new ArrayDeque<>();
	private ArrayDeque<Integer> continue$target$stack = new ArrayDeque<>();
	// za break i continue 
	
	private ArrayDeque<Integer> for$cond$start = new ArrayDeque<>();
	private ArrayDeque<Integer> for$over$start = new ArrayDeque<>();
	private ArrayDeque<Boolean> for$has$cond = new ArrayDeque<>();
	private int for$phase = 0;   // 0=ocekuje init, 1=ocekuje uslov, 2=ocekuje inkrement

	
	private ArrayDeque<List<Integer>> for$false$list = new ArrayDeque<>();
	private void forHeaderCycle() {
	    if (for$phase == 0) {
	        for$cond$start.push(Code.pc);
	        for$phase = 1;
	    } else if (for$phase == 1) {
	        if (for$has$cond.peek()) {
	            List<Integer> falseList = false$list$stack.pop();
	            List<Integer> trueList = true$list$stack.pop();
	            for (int adr : trueList) Code.fixup(adr);   
	            for$false$list.push(falseList);              
	        }
	        jmp$fix$adrr.push(code.pc + 1);
	        Code.putJump(0);
	        for$over$start.push(Code.pc);
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
	        for (int adr : for$false$list.pop()) Code.fixup(adr);
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
		code.load(obj);
		
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
		code.put2((struct.getNumberOfFields()+1) * 4);
		// *4 jer svako polje je 32b 
		
	    code.put(code.dup);
	    code.loadConst(vtable$adr.get(struct)); 
	    code.put(code.putfield);
	    code.put2(0);
	}
	
	@Override
	public void visit(DesignatorField DesignatorField) {
		//zamena objekta jer vec sam code.load(...)
		// u odnosu na kind u designator assign
	    Obj field = obj$pointers.get(DesignatorField);
	    Obj instance = designator$stack.pop();
	    if (instance.getKind() != Obj.Type) {   // preskoci load ako je baza samo ime tipa (enum)
	        code.load(instance);
	        if (field.getKind() == Obj.Meth) {
	            callBase$stack.push(instance);
	        }
	    }
	    designator$stack.push(field);
	}
	
	// za ubacivanje fake this ako je potrebno 
	private boolean methodNeedsThis(Obj meth) {
	    Iterator<Obj> it = meth.getLocalSymbols().iterator();
	    return it.hasNext() && it.next().getName().equals("this");
	}

	@Override
	public void visit(ClassDecl ClassDecl) {
		 int base = Code.dataSize;
		Struct current$class$struct = type$pointers.get(ClassDecl);
	    vtable$adr.put(current$class$struct, base);

	    int size = 0;
	    for (Obj member : current$class$struct.getMembers()) {
	        if (member.getKind() != Obj.Meth) continue;
	        size += member.getName().length() + 2;   // karakteri + (-1) + adresa
	    }
	    size += 1;   // finalni -2

	    Code.dataSize += size;
	}

@Override
public void visit(ClassDeclEmpty n) { visit((ClassDecl)n); }
@Override
public void visit(ClassDeclNoVars n) {visit((ClassDecl)n); }
@Override
public void visit(ClassDeclNoMeth n) { visit((ClassDecl)n); }
@Override
public void visit(ClassDeclVarMeth n) { visit((ClassDecl)n); }
}

