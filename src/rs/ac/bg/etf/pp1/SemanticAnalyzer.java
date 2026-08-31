package rs.ac.bg.etf.pp1;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import rs.ac.bg.etf.pp1.ast.*;
import rs.etf.pp1.symboltable.Tab;
import rs.etf.pp1.symboltable.concepts.Obj;
import rs.etf.pp1.symboltable.concepts.Struct;

public class SemanticAnalyzer extends VisitorAdaptor {
	
	//pomocna polja za izgradnju tabele
	private Struct boolType;
	private Obj program$obj; //drzi pocetni cvor programa 
	private Obj boolObj; //bool tip podatka 
	private Struct expr$type; //posle svakog expr se menja
	private Struct assing$type; //menja se na svakom '=' 
	
	
	private Set<Obj> abstractMethods = new HashSet<>(); //za proveru implementacije 
													// abs metoda klase 
	
	
	private ArrayDeque<Obj> class$methods = new ArrayDeque<>();
	private ArrayDeque<ArrayDeque<Obj>> class$methods$stack = new ArrayDeque<>();
	//za kopiranje metoda klase
	
	private ArrayDeque<List<Struct>> arg$types$stack = new ArrayDeque<>();
	//provera da li su argumenti odgovarajuceg tipa pri pozivu
	private ArrayDeque<Struct> mul$stack = new ArrayDeque<Struct>();
	private ArrayDeque<Struct> add$stack = new ArrayDeque<Struct>();
	//stack vrednosti struktura za proveru kompatibilnosti tipa podataka
	private ArrayDeque<Obj> designator$stack = new ArrayDeque<>();
	//stack za designator primer: val.c.arr  [drzi obj cvorove]
	// stack: val -> c -> arr
	
	private String current$type;// trenutni tip var , konstante, designatora
	private String current$name; // ime trenutne var , konstante, ili samog designatora 
	private Object current$value; // cuva vrednost konstante 
	
	private Obj obj$holder; // drzac za objektni cvor metode, kako bi zatvorio lanac
	private Struct struct$holder;  //drzi strukturni cvor klasa
	
	private boolean is$array = false; // postavlja se pri deklaraciji promenljive
										//konstante ili var
	private boolean part$of$class = false; // za postavljanje fld za kind
											// kod klasa
	
	
	private ArrayDeque<Set<Integer>> switch$stack = new ArrayDeque<>();//provera vrednosti case-a
	
	private int forDepth = 0;
	private int switchDepth = 0; 
	//za proveru break uslova; 
	
	private ArrayList<enum$elem> enum$list = new ArrayList<>();
	//niz u kome se cuva podatak enuma i koji je po redu
	
	
	//Pokazivaci na objektne cvorove za laksi pristup
	private Map<SyntaxNode, Obj> resolved$obj = new HashMap<>();
	public Map<SyntaxNode, Obj> getResolvedObj() {
	    return resolved$obj;
	}
	
	//Pokazivaci na strukturne cvorove 
	private Map<SyntaxNode, Struct> resolved$type = new HashMap<>();
	public Map<SyntaxNode, Struct> getResolvedType() {
	    return resolved$type;
	}
	
	private class enum$elem {
		String name; int val;
		public enum$elem(String name , int val) {
			this.name = name;
			this.val = val; 
		}
	}
	
	private void checkEnumElements(EnumDecl node) { //O(n) funkcija jer radi dodavanje u 
										// u skup pa ako se pokusa dodati postojeci element 
										// baci false sto je O(n) 
	    HashSet<String> names = new HashSet<>();
	    HashSet<Integer> values = new HashSet<>();

	    for (enum$elem e : enum$list) {
	        if (!names.add(e.name) || !values.add(e.val)) {
	            report_error(
	                "elementi u nabrajanju moraju da imaju razlicit naziv i jedinstven redni broj",
	                node
	            );
	            return;
	        }
	    }
	}
	
	
	//pomocna funkcija za proveru parametra funkcije
	
	private boolean assignCompatible(Struct src, Struct dst) {
	    
		if (src.assignableTo(dst)) return true;   // pokriva equals i null->ref slucaj
	    if (dst.getKind() == Struct.Class && src.getKind() == Struct.Class) {
	        Struct cur = src.getElemType();
	        while (cur != null && !cur.equals(Tab.noType)) {
	            if (cur.equals(dst)) return true;
	            cur = cur.getElemType();
	        }
	    }
	    return false;
	}
	
	private boolean hasThis(Obj method) {
	    var it = method.getLocalSymbols().iterator();
	    return it.hasNext() && it.next().getName().equals("this");
	}
	
	private void checkArgs(Obj method, List<Struct> argTypes) throws Exception {
	    int nParams = method.getLevel();
	    if (argTypes.size() != nParams) {
	        report_error("broj argumenata se ne poklapa kod poziva " + method.getName(), null);
	        return;
	    }
	    Iterator<Obj> it = method.getLocalSymbols().iterator();
	    int i = 0;
	    for (Struct argType : argTypes) {
	        Obj param = it.next();   // prvih nParams elemenata SU parametri, u redosledu deklaracije
	        if(param.getName().equals("this"))continue;
	        if (!assignCompatible(argType, param.getType())) {
	            throw new Exception("tip argumenta " + (i + 1) 
				+ " nije kompatibilan kod poziva " + method.getName());
	        }
	        i++;
	    }
	}
	
	//ispis greske
	public boolean errorDetected = false;
	public int errorCount = 0;
	private boolean is$void;

	private void report_error(String message, SyntaxNode info) {
		errorDetected = true;
		errorCount++;
		StringBuilder msg = new StringBuilder(message);
		int line = (info == null) ? 0 : info.getLine();
		msg.append(" na liniji ").append(line);
		System.err.println(msg.toString());
	}
	
	
	@Override
	public void visit(ProgramName ProgramName) {
		//posto jedan program je po fajlu i ime programa je odmah na pocetku
		//ovde dodajem bool constantu i pamtim pokazivac na nju 
		boolType = new Struct(Struct.Int);
		boolObj = Tab.insert(Obj.Type, "bool", boolType);
		boolObj.setLevel(-1); boolObj.setAdr(-1);
		//Program name visit//
		
		program$obj =Tab.insert(Obj.Prog, ProgramName.getI1(), Tab.noType);
		resolved$obj.put(ProgramName, program$obj);
		program$obj.setAdr(0); program$obj.setLevel(0);
		//scope za klase u programu i constante 
		Tab.openScope();
	}
	
	//resenje vise smena za tehnicki jedan terminal 
	@Override
	public void visit(ProgramMethods ProgramMethods) {
		visit((Program)ProgramMethods);
	}

	@Override
	public void visit(ProgramNoDeclList ProgramNoDeclList) {
		visit((Program)ProgramNoDeclList);
	}

	
	@Override
	public void visit(Program Program) {
		Obj main;
		if((main = Tab.currentScope.findSymbol("main")) == null)report_error("main funkcija"
				+ " nije definisana u glavnom programu", Program);
		if(main != null && main.getLevel() > 0)report_error(""
				+ "main mora da ima 0 argumenata", Program);
		Tab.chainLocalSymbols(program$obj);
		Tab.closeScope();
	}
	
	@Override
	public void visit(Type Type) {
		current$type = Type.getI1();
	}
	
	@Override
	public void visit(ConstName ConstName) {
		current$name = ConstName.getI1();
		if(Tab.currentScope().findSymbol(current$name) != null){
			report_error(current$name + " je vec definisana", ConstName);
		}
	}
	
	@Override
	public void visit(NumVal NumVal) {
		current$value = NumVal.getN1();
		expr$type = Tab.intType;
	}
	
	@Override
	public void visit(BoolVal BoolVal) {
		current$value = BoolVal.getB1();
		expr$type = boolType;
	}
	
	@Override
	public void visit(CharVal CharVal) {
		current$value = CharVal.getC1();
		expr$type = Tab.charType;
	}
	
	@Override
	public void visit(ConstItem ConstItem) {
	    if (current$type.equals("bool") || current$type.equals("char") || current$type.equals("int")) {
	        var type$pointer = Tab.find(current$type);
	        var struct = Tab.insert(Obj.Con, current$name, type$pointer.getType());
	        struct.setLevel(1);
	        if (current$type.equals("char")) {
	            try { struct.setAdr((char) current$value); }
	            catch (Exception e) { report_error("Nepoklapanje tipa i vrednosti", ConstItem); }
	        } else {
	            try { struct.setAdr((int) current$value); }
	            catch (Exception e) { report_error("Nepoklapanje tipa i vrednosti", ConstItem); }
	        }
	    } else {
	        report_error("Neodgovarajuci tip podatka za konstantu", ConstItem);
	    }
	}
	
	@Override
	public void visit(VarNameEnd VarNameEnd) {
		current$name = VarNameEnd.getI1();
		if(Tab.currentScope().findSymbol(current$name) != null){
			report_error(current$name + " je vec definisana", VarNameEnd);
		}
		else {
			if(is$array) {
				var struct$array = new Struct(Struct.Array);
				struct$array.setElementType(Tab.find(current$type).getType());
				Tab.insert(part$of$class ? Obj.Fld:Obj.Var, current$name, struct$array);
			}
			else {		
				var struct = Tab.find(current$type).getType();
				if(!struct.equals(Tab.noType)) {
				Tab.insert(part$of$class ? Obj.Fld:Obj.Var, current$name, struct);	
				}else {
					report_error(current$type + " je nepostojaci tip", VarNameEnd);
				}
			}
		}
	}
	
	@Override
	public void visit(VarNameNext VarNameNext) {
		current$name = VarNameNext.getI2();
		if(Tab.currentScope().findSymbol(current$name) != null){
			report_error(current$name + " je vec definisana", VarNameNext);
		}
		else {
			if(is$array) {
				var struct$array = new Struct(Struct.Array);
				struct$array.setElementType(Tab.find(current$type).getType());
				Tab.insert(part$of$class ? Obj.Fld:Obj.Var, current$name, struct$array);
			}else {
				var struct = Tab.find(current$type).getType();
				if(!struct.equals(Tab.noType)) {
				Tab.insert(part$of$class ? Obj.Fld:Obj.Var, current$name, struct);	
				}else {
					report_error(current$type + " je nepostojaci tip", VarNameNext);
				}
			}
		}
	}
	@Override
	public void visit(NotArray NotArray) {
		is$array = false;
	}
	@Override
	public void visit(Array Array) {
		is$array = true;
	}
	@Override
	public void visit(EnumConstNoVal EnumConstNoVal){
		try {	
			enum$list.add(new enum$elem(EnumConstNoVal.getI1(), enum$list.getLast().val + 1));
		}catch (Exception e) {
			enum$list.add(new enum$elem(EnumConstNoVal.getI1(), 0));
		}
	}
	@Override
	public void visit(EnumConstVal EnumConstVal) {
		enum$list.add(new enum$elem(EnumConstVal.getI1(),((NumVal) EnumConstVal.getNumConst()).getN1()));
	}
	
	@Override
	public void visit(EnumDecl EnumDecl) {
		current$name = EnumDecl.getI1();
		if(Tab.currentScope().findSymbol(current$name) != null){
			report_error(current$name + " je vec definisana", EnumDecl);
		}else {
		var enumType = new Struct(Struct.Enum);
		enumType.setElementType(Tab.intType);
		Tab.insert(Obj.Type, current$name, enumType);
		Tab.openScope();
		//sortiranje
		enum$list.sort(Comparator.comparingInt(e -> e.val));
		checkEnumElements(EnumDecl);
		//----------
		for (var obj:enum$list) {
			
			var inst = Tab.insert(Obj.Con, obj.name, Tab.intType);
			inst.setAdr(obj.val);
		}
		Tab.chainLocalSymbols(enumType);
		Tab.closeScope();
		enum$list.clear();
		}
	}
	@Override
	public void visit(ClassDeclEmpty ClassDeclEmpty) {
		visit((ClassDecl)ClassDeclEmpty);
	}
	@Override
	public void visit(ClassDeclNoMeth ClassDeclNoMeth) {
		visit((ClassDecl)ClassDeclNoMeth);
	}
	@Override
	public void visit(ClassDeclNoVars ClassDeclNoVars) {
		visit((ClassDecl)ClassDeclNoVars);
	}
	@Override
	public void visit(ClassDeclVarMeth ClassDeclVarMeth) {
		visit((ClassDecl)ClassDeclVarMeth);
	}
	
	@Override
	public void visit(ClassDecl ClassDecl) {
		Tab.chainLocalSymbols(struct$holder);
		Tab.closeScope();
		for(var obj : struct$holder.getMembers()) {
			if(obj.getKind() == Obj.Fld) {
				obj.setAdr(obj.getAdr() + 1);
			}
			// ostavljamo mesto za VTable ove klase 
		}
		isImplemented(struct$holder, ClassDecl);
		resolved$type.put(ClassDecl, struct$holder);
		struct$holder = null; 
		part$of$class = false; 
	}
	
	private void isImplemented(Struct concreteClass, SyntaxNode node) {
	    for (var member : concreteClass.getMembers()) {
	        if (member.getKind() == Obj.Meth && abstractMethods.contains(member)) {
	            //ulazi ovde ako je onaj isti objekat iz klase iznad
	        	//ako je redefinisan promenice se u methodname novim objektom
	        	
	        	report_error(member.getName() + " nije implementirana u ovoj klasi", node);
	        }
	    }
	}
	@Override
	public void visit(ClassName ClassName) {
		current$name = ClassName.getI1();
		if(Tab.currentScope().findSymbol(current$name) != null){
			report_error(current$name + " je vec definisana", ClassName);
		}else {			
			struct$holder = new Struct(Struct.Class);
			Tab.insert(Obj.Type, current$name, struct$holder);
			resolved$type.put(ClassName, struct$holder);
			Tab.openScope();
			part$of$class = true; 
		}
	}
	private boolean already$declared = false;
	private Obj decObj;
	@Override
	public void visit(MethodDecl MethodDecl) {
		Tab.chainLocalSymbols(obj$holder);
		Tab.closeScope();	
		 part$of$class = hasThis(obj$holder);
		if(already$declared) {
			if(obj$holder.getLevel() != decObj.getLevel()) {
				System.out.println(obj$holder.getLevel() + " " +decObj.getLevel() );
			    report_error(decObj.getName() + " ima drugaciju deklaraciju u odnosu na drugu klasu", MethodDecl);
			} else {
			    Iterator<Obj> it1 = obj$holder.getLocalSymbols().iterator();
			    Iterator<Obj> it2 = decObj.getLocalSymbols().iterator();
			    int i = 0;
			    while (i<decObj.getAdr()) {
			        var i1 = it1.next();
			        var i2 = it2.next();
			        if (i1.getName().equals("this") || i2.getName().equals("this")) continue;
			        if (!i1.getType().equals(i2.getType())) {
			            report_error(i1.getName() + " argumenti nisu istog tipa", MethodDecl);
			        }
			    }
			}
			already$declared = false;
		}
			
		obj$holder = null;
	}
	
	@Override
	public void visit(MethodDeclNoParameter MethodDeclNoParameter) {
		visit((MethodDecl)MethodDeclNoParameter);
	}
	@Override
	public void visit(MethodDeclNoVars MethodDeclNoVars) {
		visit((MethodDecl)MethodDeclNoVars);
	}
	@Override
	public void visit(MethodDeclNoVarsNoParameter MethodDeclNoVarsNoParameter) {
		visit((MethodDecl)MethodDeclNoVarsNoParameter);
	}
	@Override
	public void visit(MethodDeclVars MethodDeclVars) {
		visit((MethodDecl)MethodDeclVars);
	}
	
	
	@Override
	public void visit(MethodName MethodName) {
		current$name = MethodName.getI1();
		if(current$name.equals("main") && !is$void){
			report_error("metoda " + current$name + " mora vracati void", MethodName);
		}
		Obj obj;
		if((obj = Tab.currentScope().findSymbol(current$name)) != null){
			if(!part$of$class) {
				report_error(current$name + " je vec definisana", MethodName);
			}else {
				 var struct = Tab.find(current$type).getType();
				    Struct expectedType = is$void ? Tab.noType : struct;
				    if (!expectedType.equals(obj.getType())) {
				        report_error(current$name + " redefinicija mora imati isti povratni tip kao u baznoj klasi", MethodName);
				    }
				    decObj = obj;  
			        Tab.currentScope().getLocals().deleteKey(current$name);
			        obj$holder = Tab.insert(Obj.Meth, current$name, expectedType);
			        obj$holder.setLevel(0);

			        is$void = false;
			        Tab.openScope();
			        already$declared = true;

			        Obj this$obj = Tab.insert(Obj.Var, "this", struct$holder);
			        this$obj.setFpPos(Obj.NO_VALUE);
			}
		}
		else {
			var struct = Tab.find(current$type).getType();
			if(!struct.equals(Tab.noType) || is$void) {
				obj$holder = Tab.insert(Obj.Meth, current$name,is$void? Tab.noType:struct);
				is$void = false;
				obj$holder.setLevel(0);
				Tab.openScope();
	            if (part$of$class) {
	                Obj this$obj = Tab.insert(Obj.Var, "this", struct$holder);
	                this$obj.setFpPos(Obj.NO_VALUE);
	            }
			}
			else {
				report_error(current$type + " je nepostojaci tip", MethodName);
			}
		}
		resolved$obj.put(MethodName, obj$holder); 
		part$of$class = false;
	}
	@Override
	public void visit(MethodVoid MethodVoid) {
		is$void = true;
	}
	@Override
	public void visit(ParameterName ParameterName) {
		
		current$name = ParameterName.getI1();
		if(Tab.currentScope().findSymbol(current$name) != null){
			report_error(current$name + " je vec parametar metode", ParameterName);
		}else {
			Struct struct;
			if(!is$array) struct = Tab.find(current$type).getType();
			else {	
				struct = new Struct(Struct.Array);
				struct.setElementType(Tab.find(current$type).getType());
			}
			if(!struct.equals(Tab.noType)) {
				obj$holder.setLevel(obj$holder.getLevel() + 1);
				var paramObj = Tab.insert(Obj.Var, current$name, struct);
				paramObj.setFpPos(obj$holder.getLevel() - 1);  
				paramObj.setLevel(1);
			}else {
				report_error(current$type + " je nepostojaci tip", ParameterName);
			}
		}
	}
	@Override
	public void visit(AbstractClassDecl AbstractClassDecl) {
		Tab.chainLocalSymbols(struct$holder);
		Tab.closeScope();
		for(var obj : struct$holder.getMembers()) {
			if(obj.getKind() == Obj.Fld) {
				obj.setAdr(obj.getAdr() + 1);
			}
			// ostavljamo mesto za VTable ove klase 
		}
		resolved$type.put(AbstractClassDecl, struct$holder);
		struct$holder = null;
	}
	@Override
	public void visit(AbstractClassDeclEmpty AbstractClassDeclEmpty) {
		visit((AbstractClassDecl)AbstractClassDeclEmpty);
	}
	@Override
	public void visit(AbstractClassDeclNoMeth AbstractClassDeclNoMeth) {
		visit((AbstractClassDecl)AbstractClassDeclNoMeth);
	}
	@Override
	public void visit(AbstractClassDeclNoVars AbstractClassDeclNoVars) {
		visit((AbstractClassDecl)AbstractClassDeclNoVars);
	}
	@Override
	public void visit(AbstractClassDeclVarMeth AbstractClassDeclVarMeth) {
		visit((AbstractClassDecl)AbstractClassDeclVarMeth);
	}
	
	@Override
	public void visit(AbstractMethodDecl AbstractMethodDecl) {
		Tab.chainLocalSymbols(obj$holder);
		Tab.closeScope();
		part$of$class = hasThis(obj$holder);
		abstractMethods.add(obj$holder);
		obj$holder = null;
	}
	@Override
	public void visit(AbstractMethodDeclNoPars AbstractMethodDeclNoPars) {
		visit((AbstractMethodDecl)AbstractMethodDeclNoPars);
	}
	@Override
	public void visit(AbstractMethodDeclVars AbstractMethodDeclVars) {
		visit((AbstractMethodDecl)AbstractMethodDeclVars);
	}
	
	@Override
	public void visit(ExtendsToType ExtendsToType) {
		Obj object = Tab.find(ExtendsToType.getType().getI1());
		if(object.equals(Tab.noObj)) {
				report_error(ExtendsToType.getType().getI1() + " je nepostojaci Tip", ExtendsToType);
			}
		else if (object.getKind() != Obj.Type) {
			report_error(ExtendsToType.getType().getI1() + " nije tip koji je moguce prosiriti", ExtendsToType);
		}
		else if(object.getType().getKind() != Struct.Class) {
			report_error(ExtendsToType.getType().getI1() + " nije klasa", ExtendsToType);
		}
		else {
			var struct = object.getType();
			struct$holder.setElementType(struct);
			ArrayDeque<Obj> arr = new ArrayDeque<>();;
			for(var member : struct.getMembers()) {
				if(member.getKind() == Obj.Fld)
					Tab.insert(member.getKind(),member.getName(), member.getType());				
				else if(member.getKind() == Obj.Meth) {
					arr.add(member);
				}
			}
			class$methods$stack.add(arr);
		}
	}
	
	@Override
	public void visit(CopyMethods CopyMethods) {
	    if (!class$methods$stack.isEmpty()) {
	        class$methods = class$methods$stack.pop();
	        while (!class$methods.isEmpty()) {
	            var method = class$methods.pop();
	            Tab.currentScope().addToLocals(method);   // ISTA instanca, ne nova!
	        }
	        class$methods.clear();
	    }
	    class$methods = null;
	}
	
	@Override
	public void visit(DesignatorIdent DesignatorIdent) {
	    current$name = DesignatorIdent.getI1();
	    Obj obj = Tab.find(current$name);
	    if (obj.equals(Tab.noObj)) {
	        report_error(current$name + " nije definisana", DesignatorIdent);
	    }
	    designator$stack.push(obj);
	    resolved$obj.put(DesignatorIdent, obj);
	    expr$type = obj.getType();
	}
	
	@Override
	public void visit(DesignatorField DesignatorField) {
	    current$name = DesignatorField.getI2();
	    Obj base = designator$stack.pop();
	    if (base.getType().getKind() == Struct.Class || base.getType().getKind() == Struct.Enum) {
	    	Obj found;
	    	if(base.getName().equals("this")) {
	    		found = Tab.currentScope.getOuter().findSymbol(current$name);
	    		//jer je otvoren scope za metodu klase pa time mora da se vratimo
	    		// jos jedan scope iznad u kojoj su svi fld i methode te klase pa
	    		//da potrazimo da li zapravo postoji to polje 
	    	}else {
	    		found = base.getType().getMembersTable().searchKey(current$name);
	    	}
	    	
	        if (found == null) {
	            report_error(current$name + " nije polje klase " + base.getName(), DesignatorField);
	            designator$stack.push(Tab.noObj);
	        } else {
	            designator$stack.push(found);
	            resolved$obj.put(DesignatorField, found);
	            expr$type = found.getType();
	        }
	    } else {
	        report_error(current$name + " nije objekat klase", DesignatorField);
	        designator$stack.push(Tab.noObj);
	    }
	}
	
	@Override
	public void visit(DesignatorAssign DesignatorAssign) {
		
	    if (!assignCompatible(expr$type, assing$type)) {
//	    	if(assing$type.getKind()== Struct.Array)assing$type =assing$type.getElemType();
//	    	if(expr$type.getKind() == Struct.Array)expr$type = expr$type.getElemType();
	    	  report_error("tip izraza nije kompatibilan sa tipom promenljive pri dodeli", DesignatorAssign);
	    }
	}
	@Override
	public void visit(DesignatorLength DesignatorLength) {
	    Obj base = designator$stack.pop();
	    if (base.getType().getKind() == Struct.Array) {
	        designator$stack.push(Tab.lenObj);
	    } else {
	        report_error(current$name + " nije niz", DesignatorLength);
	        designator$stack.push(Tab.noObj);
	    }
	}
	
	@Override
	public void visit(DesignatorInc DesignatorInc) {
	    Obj target = designator$stack.pop();
	    if (!target.getType().equals(Tab.intType)) {
	        report_error(current$name + " nije tipa int", DesignatorInc);
	    }
	}
	@Override
	public void visit(DesignatorDec DesignatorDec) {
	    Obj target = designator$stack.pop();
	    if (!target.getType().equals(Tab.intType)) {
	        report_error(current$name + " nije tipa int", DesignatorDec);
	    }
	}
	


	public void visit(FactorNewArray factorNewArray){
		try {
			current$name = factorNewArray.getType().getI1();
			var type = Tab.find(current$name).getType();
			int kind = type.getKind();
			if (kind != Struct.Int && kind != Struct.Char && kind != Struct.Enum && kind != Struct.Class) {
			    report_error("niz mora biti tipa int, char, bool ili nabrajanje", factorNewArray);
			} else {
			    expr$type = new Struct(Struct.Array);
			    expr$type.setElementType(type);
			    resolved$type.put(factorNewArray, type);
			}
		}
		catch (Exception e) { 
			//nesto baca ovaj exception al 
			//ne znam sta bese, a smislio sam bolji nacin za resavanje
			//ovoga, NIJE BUG DA JE PRAZAN I TREBA DA BUDE 
		}
	}
	
	@Override
	public void visit(FactorNewObj FactorNewObj) {
		var type = Tab.find(current$type);
		if(type.equals(Tab.noObj))report_error(current$type + " nije postojaci tip", FactorNewObj);
		else {
			if(type.getType().getKind() != Struct.Class)report_error(current$type + " nije tip klase", FactorNewObj);
			else {
				resolved$type.put(FactorNewObj, type.getType());
			}
		}
	}
	
	@Override
	public void visit(Mulop Mulop) {
		mul$stack.push(expr$type);
	}
	@Override
	public void visit(MulopMUL MulopMUL) {
		visit((Mulop)MulopMUL);
	}
	public void visit(MulopDIV mulopDIV){
		visit((Mulop)mulopDIV);
	}
	@Override
	public void visit(MulopMOD MulopMOD) {
		visit((Mulop)MulopMOD);
	}
	@Override
	public void visit(TermMul TermMul) {
	    Struct left = mul$stack.pop();
	    if (!left.equals(Tab.intType) || !expr$type.equals(Tab.intType)) {
	        report_error("nisu oba operanda tipa int kod mnozenja", TermMul);
	    }
	    expr$type = Tab.intType;
	}
	
	@Override
	public void visit(FactorDesignator FactorDesignator) {
	    Obj o = designator$stack.pop();
	    expr$type = o.getType();
	}
//	@Override
//	public void visit(FactorDesignator FactorDesignator) {
//		//expr$type = designator$obj.getType();
//	}
//	BUG popravlja prva ideja stavljanja kod DesignatorIdenta 
	@Override
	public void visit(AddExprNeg AddExprNeg) {
		if(!expr$type.equals(Tab.intType)) report_error("izraz nije tipa int", AddExprNeg);
	}
	
	@Override
	public void visit(AddopADD AddopADD) {
		visit((Addop)AddopADD);
	}
	@Override
	public void visit(AddopMIN AddopMIN) {
		visit((Addop)AddopMIN);
	}
	@Override
	public void visit(Addop Addop) {
		add$stack.push(expr$type);
	}
	@Override
	public void visit(AddExprAdd AddExprAdd) {
	    Struct left = add$stack.pop();
	    if (!left.equals(Tab.intType) || !expr$type.equals(Tab.intType)) {
	        report_error("nisu oba operanda tipa int kod sabiranja", AddExprAdd);
	    }
	    expr$type = Tab.intType;
	}
	@Override
	public void visit(DesignatorArrayElem DesignatorArrayElem) {
	    Obj base = designator$stack.pop();
	    if (base.getType().getKind() != Struct.Array) {
	        report_error(current$name + " nije niz", DesignatorArrayElem);
	        designator$stack.push(Tab.noObj);
	        return;
	    }
	    if (expr$type.getKind() != Struct.Int) {
	        report_error("indeks niza mora biti tipa int", DesignatorArrayElem);
	    }
	    designator$stack.push(new Obj(Obj.Elem, base.getName(), base.getType().getElemType()));
	}
	

	@Override
	public void visit(StatementFindAny StatementFindAny) {
	    Obj rhsArray = designator$stack.pop();

	    if (!assing$type.equals(boolType)) {
	        report_error("leva strana findAny mora biti tipa bool", StatementFindAny);
	    }
	    if (rhsArray.getType().getKind() != Struct.Array) {
	        report_error("desna strana findAny mora biti niz", StatementFindAny);
	    } else {
	        Struct elemType = rhsArray.getType().getElemType();
	        int k = elemType.getKind();
	        if (k != Struct.Int && k != Struct.Char) {
	            report_error("findAny radi samo nad nizovima ugradjenog tipa", StatementFindAny);
	        }
	        if (!expr$type.equals(elemType)) {
	            report_error("izraz u findAny mora biti istog tipa kao elementi niza", StatementFindAny);
	        }
	    }

	}
	
	@Override
	public void visit(Assignop Assignop) {
	    Obj target = designator$stack.pop();
	    int kind = target.getKind();
	    if (kind != Obj.Var && kind != Obj.Fld && kind != Obj.Elem) {
	        report_error(target.getName() + " ne moze biti meta dodele", Assignop);
	    }

	    assing$type = target.getType();
	    designator$stack.clear();
	}

	@Override
	public void visit(ActParsEnd ActParsEnd) {
	    List<Struct> args = new ArrayList<>();
	    args.add(expr$type);
	    arg$types$stack.push(args);
	}

	@Override
	public void visit(ActParsNext ActParsNext) {
	    arg$types$stack.peek().add(expr$type);
	}

	private void finishCall(SyntaxNode node, boolean hasArgs) throws Exception {
		Obj method = designator$stack.pop();
	    List<Struct> args = hasArgs ? arg$types$stack.pop() : new ArrayList<>();
	    if (method.getKind() != Obj.Meth) {
	    	throw new Exception(current$name + " nije metoda");

	    }
		checkArgs(method, args);
	    expr$type = method.getType();
	}

	@Override
	public void visit(FactorCallPars FactorCallPars) { 
		try {
			finishCall(FactorCallPars, true);
		} catch (Exception e) {
	        report_error(e.getMessage(), FactorCallPars);
	        expr$type = Tab.noType;
		}
		
	}
	@Override
	public void visit(FactorCallNoPars FactorCallNoPars) { 
		try {
			finishCall(FactorCallNoPars, false);
		} catch (Exception e) {
			report_error(e.getMessage(), FactorCallNoPars);
	        expr$type = Tab.noType;
		} 
	}
	@Override
	public void visit(DesignatorCallPars DesignatorCallPars) { 
			try {
				finishCall(DesignatorCallPars, true);
			} catch (Exception e) {
				report_error(e.getMessage(), DesignatorCallPars);
		        expr$type = Tab.noType;
			} 
		}
	@Override
	public void visit(DesignatorCallNoPars DesignatorCallNoPars) {
		try {
			finishCall(DesignatorCallNoPars, false);
		} catch (Exception e) {
			report_error(e.getMessage(), DesignatorCallNoPars);
	        expr$type = Tab.noType;
		} 
	}
	
	
	
	//statment visits 
	
	@Override
	public void visit(StatementReturn StatementReturn) {
		if(!obj$holder.getType().equals(Tab.noType)) {
			report_error(obj$holder.getName() + " ima povratnu vrednost", StatementReturn);
		}
	}
	@Override
	public void visit(StatementReturnExpr StatementReturnExpr) {
		if(!assignCompatible( expr$type,obj$holder.getType())) {
			
			report_error("povratna vrednost funkcije ["+obj$holder.getType().getKind() + "]" + obj$holder.getName() +
					" i return vrednost nemaju kompatibilne "
					+ "tipove", StatementReturnExpr);
		}
	}
	@Override
	public void visit(StatementRead StatementRead) {
	    Obj obj = designator$stack.pop();
	    if (obj.equals(Tab.noObj)) return;   // greska je vec prijavljena ranije u lancu, ne dupliraj

	    int kind = obj.getKind();
	    if (kind != Obj.Var && kind != Obj.Fld && kind != Obj.Elem) {
	        report_error("Designator mora oznacavati promenljivu, element niza ili polje unutar objekta", StatementRead);
	        return;
	    }

	    int typeKind = obj.getType().getKind();
	    if (typeKind != Struct.Int && typeKind != Struct.Char) {
	        report_error("Designator u read() mora biti tipa int, char ili bool", StatementRead);
	    }
	}
	
	
	@Override
	public void visit(ForHeader ForHeader) {
	    forDepth++;
	}

	@Override
	public void visit(StatementFor StatementFor) {
	    forDepth--;
	  
	}

	@Override
	public void visit(StatementBreak StatementBreak) {
	    if (forDepth == 0 && switchDepth == 0) {
	        report_error("break se moze koristiti samo unutar for petlje ili switch bloka", StatementBreak);
	    }
	}

	@Override
	public void visit(StatementContinue StatementContinue) {
	    if (forDepth == 0) {
	        report_error("continue se moze koristiti samo unutar for petlje", StatementContinue);
	    }
	}
	
	
	@Override
	public void visit(StatementPrint StatementPrint) {
	    int kind = expr$type.getKind();
	    if (kind != Struct.Int && kind != Struct.Char) {
	        report_error("izraz u print() mora biti tipa int, char ili bool", StatementPrint);
	    }
	}

	@Override
	public void visit(StatementPrintWidth StatementPrintWidth) {
	    int kind = expr$type.getKind();
	    if (kind != Struct.Int && kind != Struct.Char) {
	        report_error("izraz u print() mora biti tipa int, char ili bool", StatementPrintWidth);
	    }
	}
	


	@Override
	public void visit(SwitchHeader SwitchHeader) {
	    if (!expr$type.equals(Tab.intType)) {
	        report_error("izraz u switch mora biti tipa int", SwitchHeader);
	    }
	    switchDepth++;
	    switch$stack.push(new HashSet<>());
	}

	@Override
	public void visit(StatementSwitch StatementSwitch) {
	    switchDepth--;
	    switch$stack.pop();
	}

	@Override
	public void visit(CaseStmt CaseStmt) {
	    int value = ((NumVal) CaseStmt.getNumConst()).getN1();
	    if (!switch$stack.peek().add(value)) {
	        report_error("case vrednost " + value + " je vec koriscena u ovom switch bloku", CaseStmt);
	    }
	}
	
	@Override
	public void visit(CondTermAnd CondTermAnd) {
	    expr$type = boolType; 
	}
	@Override
	public void visit(ConditionOr ConditionOr) {
	    expr$type = boolType;
	}
	
	
	private ArrayDeque<Struct> relLeft$stack = new ArrayDeque<>();
	private ArrayDeque<Boolean> relEq$stack = new ArrayDeque<>();

	private void pushRelop(boolean isEquality) {
	    relLeft$stack.push(expr$type);
	    relEq$stack.push(isEquality);
	}

	@Override
	public void visit(RelopEQ RelopEQ) { pushRelop(true); }    // ==
	@Override
	public void visit(RelopNEQ RelopNEQ) { pushRelop(true); }    // !=
	@Override
	public void visit(RelopLE RelopLE) { pushRelop(false); }
	@Override
	public void visit(RelopLT RelopLT) { pushRelop(false); }
	@Override
	public void visit(RelopGT RelopGT) { pushRelop(false); }
	@Override
	public void visit(RelopGE RelopGE) { pushRelop(false); }

	@Override
	public void visit(CondFactRel CondFactRel) {
	    Struct left = relLeft$stack.pop();
	    boolean isEquality = relEq$stack.pop();
	    Struct right = expr$type;

	    if (!left.compatibleWith(right)) {
	        report_error("operandi relacionog operatora nisu kompatibilnog tipa", CondFactRel);
	    } else if ((left.getKind() == Struct.Class || left.getKind() == Struct.Array) && !isEquality) {
	        report_error("uz promenljive tipa klase ili niza mogu se koristiti samo != i ==", CondFactRel);
	    }
	    expr$type = boolType;
	}
	
	
	@Override
	public void visit(CondFactExpr CondFactExpr) {
	    if (!expr$type.equals(boolType)) {
	        report_error("uslov mora biti tipa bool", CondFactExpr);
	    }
	    expr$type = boolType;
	}
	
	//.MAP
	private String lambda$name;
	
	@Override
	public void visit(IdentName IdentName) {
	    lambda$name = IdentName.getI1();
	}

	@Override
	public void visit(MapArrow MapArrow) {
	    Obj arr = designator$stack.pop();

	    if (arr.getType().getKind() != Struct.Array) {
	        report_error("desna strana map mora biti niz", MapArrow);
	        resolved$obj.put(MapArrow, Tab.noObj);
	        return;
	    }
	    Struct elemType = arr.getType().getElemType();

	    Obj ident = Tab.find(lambda$name);
	    if (ident.equals(Tab.noObj)) {
	        report_error(lambda$name + " nije definisana", MapArrow);
	    } else if (ident.getKind() != Obj.Var && ident.getKind() != Obj.Fld) {
	        report_error(lambda$name + " mora biti promenljiva", MapArrow);
	    } else if (!ident.getType().equals(elemType)) {
	        report_error(lambda$name + " mora biti istog tipa kao elementi niza", MapArrow);
	    }

	    resolved$obj.put(MapArrow, ident);   // ista mapa koju vec koristis - novi kljuc
	}

	@Override
	public void visit(StatementMap StatementMap) {
	    if (assing$type.getKind() != Struct.Array) {
	        report_error("leva strana map mora biti niz", StatementMap);
	        return;
	    }
	    if (!expr$type.equals(assing$type.getElemType())) {
	        report_error("izraz u map mora biti istog tipa kao elementi rezultujuceg niza", StatementMap);
	    }
	}
	
}
