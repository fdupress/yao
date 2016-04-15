#!/usr/bin/env python
import re
import sys
import random

def wireA(g,ins,gs):
    (inarity,outarity,in_w,out_w,gate,q) = g
    inp = in_w[0]
    if (inp < ins):
        return str(inp)
    else:
        (_a,_b,_c,_d,_e,feedw) = (filter(lambda (_a,_b,_c,o,_d,_e): o[0] == inp,gs))[0]
        assert feedw < q
        return str(feedw + ins)
       
def wireB(g,ins,gs):
    (inarity,outarity,in_w,out_w,gate,q) = g
    if (inarity == 1):
        inp = in_w[0]
    else:
        inp = in_w[1]
    if (inp < ins):
        return str(inp)
    else:
        (_a,_b,_c,_d,_e,feedw) = (filter(lambda (_a,_b,_c,o,_d,_e): o[0] == inp,gs))[0]
        assert feedw < q
        return str(feedw+ins)
        
def truthT(g):
    (inarity,outarity,in_w,out_w,gate,q) = g
    if gate == "AND": 
        return "0001"
    elif gate == "OR": 
        return "0111"
    elif gate == "INV": 
        return "1000"
    elif gate == "XOR": 
        return "0110"
    assert false

def outputGates(gs, outstart, outs,ins):
    wires = []
    gates = []
    for i in range(outstart,outstart+outs):
        (_a,_b,_c,_d,_e,outw) = (filter(lambda (_a,_b,_c,o,_d,_e): o[0] == i,gs))[0]
        wires.append(str(outw+ins))
        gates.append("0001")
    return (wires,gates)

def randT():
    rg = random.SystemRandom() 
    e = rg.randint (0,0xffffffffffffffffffffffffffffffff)
    return '%032x' % e

def randG():
    rg = random.SystemRandom() 
    q = 144962705535376630851503695750545784187239740224120004924293803406851036318261835673962115555390996927758933360991171299273355684194460845420775184654328585736174625520009570808425032166489646851140687881975462962428197855236374463667498288131830086834971822404235777398914601124760530698471336272308368739267L
    e = rg.randint (0,q-1)
    return str(e)

def randBit():
    rg = random.SystemRandom() 
    b = rg.randint (0,1)
    return str(b)


if len(sys.argv) != 3:
    print("Usage: sfe_example_generator <input_file> <output_file>")
    sys.exit(1)

with open(sys.argv[1]) as in_f, open(sys.argv[2], "w") as out_f:
    flines = in_f.readlines()
    line0vals = re.sub(' +',' ',flines[0]).split(" ")
    ngates = int(line0vals[0])
    nwires = int(line0vals[1])
    line1vals = re.sub(' +',' ',flines[1]).split(" ")
    in1wires = int(line1vals[0])
    in2wires = int(line1vals[1])
    outwires = int(line1vals[2])
    flines = flines[3:]
    gates = []
    q = 0
    for line in flines:
        linevals = re.sub(' +',' ',line).split(" ")
        if len(linevals) < 5:
            break
        gate = linevals[len(linevals)-1]
        gate = gate.strip('\n')
        inarity = int(linevals[0])
        if (inarity < 1) or (inarity > 2):
            print ("Input arity arror!\n")
            exit(1)
        outarity = int(linevals[1])
        if (outarity <> 1):
            print ("Output arity arror!\n")
            exit(1)
        in_w = map(int,linevals[2:2+inarity])
        out_w = map(int,linevals[2+inarity:2+inarity+outarity])
        gates.append((inarity,outarity,in_w,out_w,gate,q))
        q = q + 1
    assert q == ngates
    (extraw,extrag) = outputGates(gates,nwires-outwires, outwires,in1wires+in2wires)
    input_wires = in1wires+in2wires
    output_wires = outwires
    gate_count = ngates + outwires
    Alist = map (lambda g: wireA(g,input_wires,gates), gates) + extraw
    Blist = map (lambda g: wireB(g,input_wires,gates), gates) + extraw
    Glist = map (lambda g: truthT(g), gates) + extrag
    #randomTokens = [ randT() for i in range(2*(input_wires + gate_count)) ]
    #randomGElems1 = [ randG() for i in range(in1wires) ]
    #randomGElems2 = [ randG() for i in range(in1wires) ]
    #randomGElem2ex = randG()
    #out_f.write("i1 = <fill " + str(in1wires) + "-bit input1 in binary>\n")
    #out_f.write("i2 = <fill " + str(in2wires) + "-bit input2 in binary>\n")
    #randomI1 = [ randBit() for i in range(in1wires) ]
    #out_f.write("i1 = ")
    #for b in randomI1:
    #    out_f.write(b)
    #out_f.write("\n")  
    out_f.write("i1<"+str(in1wires)+">\n")
    #randomI2 = [ randBit() for i in range(in2wires) ]
    #out_f.write("i2 = ")
    #for b in randomI2:
    #    out_f.write(b)
    #out_f.write("\n")  
    out_f.write("i2<"+str(in2wires)+">\n")    
    out_f.write("fn = " + str(input_wires) + "; " + str(output_wires) + "; " + str(gate_count) + "; ")
    for a in Alist:
        out_f.write(" " + a)
    out_f.write(";")    
    for b in Blist:
        out_f.write(" " + b)
    out_f.write(";")    
    for g in Glist:
        out_f.write(" " + g)
    out_f.write("\n")
    #out_f.write("r1 =")
    #for e in randomGElems1:
    #    out_f.write(" " + e)
    #out_f.write("\n")
    #out_f.write("r2 =")
    #for e in randomGElems2:
    #    out_f.write(" " + e)
    #out_f.write("; " + randomGElem2ex + ";")
    #for t in randomTokens:
    #    out_f.write(" " + t)
    #out_f.write("\n")
