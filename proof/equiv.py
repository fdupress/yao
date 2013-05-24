from sys import stdin
from re import match, DOTALL, findall

eq = stdin.read()
eq = eq.replace("\n", "")
eq = eq.replace("<top>.", "")

regexEquiv = r"equiv \[(.*) ~ (.*) : (.*) ==> (.*)\]"
regexLine = r"([^;{}]*;|[^;{}]* [{][^}]*[}])"

m = match(regexEquiv, eq)
print(m.group(3))
print()
m1 = findall(regexLine, m.group(1))
m2 = findall(regexLine, m.group(2))
n1 = len(m1)
n2 = len(m2)
if n1 < n2:
  m1 = m1 + (n2-n1)*[""]
else:
  m2 = m2 + (n1-n2)*[""]
size = str(min(80, max(map(len, m1))))
for i in range(len(m1)):
  print(("{i:3}: {left:"+size+"} | {right}").format(i=i+1, left=m1[i], right=m2[i]))
print()
print(m.group(4))
