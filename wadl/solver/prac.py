class Obj1():
    # check immutable
    def __init__(self):
        self.var = 20
        self.var2 = 40
    
    def createDict(self):
        self.d = dict()
        for i in range(20):
            self.d[i] = self.var

    def changeVar(self):
        self.var = self.var2

class Obj2():
    # check immutable
    def __init__(self):
        self.var = 20
        self.var2 = 40
    
    def createDict(self):
        self.d = dict()
        for i in range(20):
            self.d[i] = self.var

    def changeVar(self):
        self.var = self.var2


x = Obj1()
x.createDict()
x.changeVar()

print(x.var)