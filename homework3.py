import re
import copy
import os


class LogicEngine:

    def __init__(self):
        self.queryCount = 0
        self.sentenceCount = 0
        self.ask = []

        self.KB = []
        self.predicateSymbolsDict = {}
        self.loopDetector = {}
        self.KBDict = {}
        self.currentAns = False

        self.oldKB = []

        self.ans = []

    def writeOutput(self, answersList):
        boolOutput = []

        for output in answersList:
            if output == None or not output:
                boolOutput.append("FALSE\n")
            if output:
                boolOutput.append("TRUE\n")

        with open("output.txt", 'w') as f:
            for index, value in enumerate(boolOutput):
                if index == len(boolOutput)-1:
                    f.write(boolOutput[index].rstrip())
                else:
                    f.write(boolOutput[index])

    def readData(self, file):
        with open(file) as f:
            inputData = f.readlines()
            self.queryCount = int(inputData[0])
            for i in range(1, self.queryCount+1):
                self.ask.append(inputData[i])

            self.sentenceCount = int(inputData[self.queryCount+1])

            startIndex = self.queryCount + 2

            while(startIndex < len(inputData)):
                self.KB.append(inputData[startIndex])
                startIndex +=1

        self.ask = [a.replace(" ", "").strip() for a in self.ask]
        self.KB = [k.replace(" ", "").strip() for k in self.KB]


        self.oldKB = copy.deepcopy(self.KB)

    '''
    predicateSymbols {F:[ ... , ... , ... ]  , G:[... , ... , ....],
    tempBoard = [x[:] for x in currentBoardState]
    '''
    def reInitValues(self):
        self.KB = copy.deepcopy(self.oldKB)
        self.loopDetector = {}
        self.currentAns = False

    def preProcessKB(self):
        self.predicateSymbolsDict = {}
        self.KBDict = {}

        for ruleID, rule in enumerate(self.KB):
            self.KBDict[rule] = len(self.KBDict)

            if "|" in rule:
                predicateSymbols = [p.split("(")[0] for p in [r.strip() for r in rule.split("|")]]
                for predicateSymbol in predicateSymbols:
                    if predicateSymbol not in self.predicateSymbolsDict:
                        self.predicateSymbolsDict[predicateSymbol] = [ruleID]
                    else:
                        self.predicateSymbolsDict[predicateSymbol] += [ruleID]

            else:
                predicateSymbol = rule.split("(")[0]
                if predicateSymbol not in self.predicateSymbolsDict:
                    self.predicateSymbolsDict[predicateSymbol] = [ruleID]
                else:
                    self.predicateSymbolsDict[predicateSymbol] += [ruleID]


    def insertSentenceIntoKB(self, newfact):
        """
        :param fact: new fact that was inferred should be added to the KB
        :return: Nothing
        """
        if newfact not in self.KBDict:
            self.KB.append(newfact)
            self.KBDict[newfact] = len(self.KBDict)
            # self.updatePredicateSymbolDict(newfact=newfact)

    def updatePredicateSymbolDict(self, newfact):

        if "|" in newfact:
            predicateSymbols = [p.split("(")[0] for p in [r.replace(" ", "") for r in newfact.split("|")]]
            for predicateSymbol in predicateSymbols:
                if predicateSymbol not in self.predicateSymbolsDict:
                    self.predicateSymbolsDict[predicateSymbol] = [self.KBDict[newfact]]
                else:
                    self.predicateSymbolsDict[predicateSymbol] += [self.KBDict[newfact]]

        else:
            predicateSymbol = newfact.replace(" ", "").split("(")[0]
            if predicateSymbol not in self.predicateSymbolsDict:
                self.predicateSymbolsDict[predicateSymbol] = [self.KBDict[newfact] ]
            else:
                self.predicateSymbolsDict[predicateSymbol] += [self.KBDict[newfact]]


    def negate(self, alpha):
        if alpha[0] == "~":
            return alpha[1:]
        return "~" + alpha

    def isConstant(self, str):
        if str[0].upper() == str[0]:
            return True
        return False

    def isVariable(self, str):
        if str[0].lower() == str[0]:
            return True
        return False

    def createBackPredicate(self, oldPredicatesDict, sigma):
        """
        :param oldPredicatesDict:
        :param sigma:
        :return:
        """
        newSentence = ""
        for predSymbol, args in oldPredicatesDict.items():
            predicate = predSymbol + "("
            for arg in args:
                if arg in sigma:
                    predicate+= sigma[arg] + ","
                else:
                    predicate +=  arg + ","

            newSentence += predicate[:-1] + ")" + "|"

        newSentence = newSentence[:-1].rstrip()

        return newSentence

    def verifySigmaOK(self, sigma):
        sigmaOK = False
        for key, value in sigma.items():
            if self.isConstant(key) or self.isConstant(value):
                sigmaOK = True
                break

        return sigmaOK

    def substitute(self, s1SearchPredicate, s1searchPredicateArguments, s2args, predicatesDict):
        """
        :param s1PredSymbol:
        :param s1args:
        :param s2args:
        :param predicatesDict:
        :return:
        """

        sigma = {}  # of the form x:Tom or Tom:Tom, or x:y
        boolUnifyPossible = True

        #note you would unify the following Tom and Tom, x and y, x and Tom
        for a1, a2 in zip(s1searchPredicateArguments, s2args):
            if (self.isVariable(a1) and self.isConstant(a2)):
                if a1 in sigma:
                    currentValueofVar = sigma[a1]
                    if a2 != currentValueofVar:
                        return None
                sigma[a1] =  a2
            if (self.isVariable(a2) and self.isConstant(a1)):
                if a2 in sigma:
                    currentValueofVar = sigma[a2]
                    if a1 != currentValueofVar:
                        return None
                sigma[a2] = a1

            if (self.isConstant(a1) and self.isConstant(a2)):
                if a1==a2:  # Tom=Tom
                    sigma[a1] = a2
                else:
                    boolUnifyPossible = False
                    break

            if (self.isVariable(a1) and self.isVariable(a2)):
                if a1 in sigma:
                    currentValueofVar = sigma[a1]
                    if a2 !=currentValueofVar:
                        return None
                sigma[a1] = a2

        if  not boolUnifyPossible:
            return None

        # if not (self.verifySigmaOK(sigma)):
        #     print("UNIFICATION FAILED: pure var subs")
        #     return None

        del predicatesDict[s1SearchPredicate]

        if len(predicatesDict) == 0:
            return "{}"

        newSentence = self.createBackPredicate(oldPredicatesDict = predicatesDict, sigma=sigma)
        return newSentence

    def standardize(self, sentence1, predicatesDict):
        """

        :param sentence1:
        :param predicatesDict:
        :return:
        """

        variableArgumenetsSenctence1 = set()
        if "|" in sentence1:
            predicatesList = sentence1.split("|")
            for predicate in predicatesList:
                _, arguments = self.getPredicateSymbolandArguments(predicate=predicate)
                for arg in arguments:
                    if self.isVariable(arg):
                        variableArgumenetsSenctence1.add(arg)
        else:
            _, arguments = self.getPredicateSymbolandArguments(predicate=sentence1)
            for arg in arguments:
                if self.isVariable(arg):
                    variableArgumenetsSenctence1.add(arg)

        replacementDict = {}
        for predicateSymbol, arguments in predicatesDict.items():
            for variable in  list(variableArgumenetsSenctence1):
                replacementVar = variable
                if variable in arguments:
                    k = 1
                    while replacementVar*k in variableArgumenetsSenctence1:
                        k = k+1
                        replacementVar = replacementVar*(k)

                    replacementDict[variable] = replacementVar

        for predicateSymbol, arguments in predicatesDict.items():
            newArgs = []
            for arg in arguments:
                if arg in replacementDict:
                    newArgs.append(replacementDict[arg])
                else:
                    newArgs.append(arg)

            predicatesDict[predicateSymbol] = newArgs


        return sentence1, predicatesDict, replacementDict


    def getNormalSentenceForm(self, newSentence):
        if newSentence == None:
            return None

        normalSentenceForm = ""

        if "|" in newSentence:
            newSentenceList = list(set(newSentence.strip().split("|")))
            for predicate in newSentenceList:
                if "_" in predicate:
                    normalpredicate  = predicate.split("_")[0] + "(" +  predicate.split("(")[1]
                else:
                    normalpredicate = predicate

                normalSentenceForm += normalpredicate+"|"

            return normalSentenceForm[:-1]
        else:
            if "_" in newSentence:
                normalSentenceForm = newSentence.split("_")[0] + "(" + newSentence.split("(")[1]
            else:
                normalSentenceForm = newSentence

            return normalSentenceForm


    def unify(self, sentence1, predicatesDict,sentence2RepeatPred):
        '''
        :param sentence1: This is what we have already proved as a part of our previous resolve step
        :param predicatesDict: this is new compatible sentence we chose to unify with sentence1. Note this is one of the many compatible
                               sentences. The chosen sentence has been passed in form of a dict
        :return: unified sentence if any
        '''

        sentence1, predicatesDict, replacementDict = self.standardize(sentence1, predicatesDict)

        # print("unify:", sentence1, '<== with ==> ', predicatesDict, "using ", replacementDict)

        sentence1RepeatPred = False

        if "|" not in sentence1 and (len(predicatesDict) ==1 or len(predicatesDict)>1) :
            predicateSymbol, arguments = self.getPredicateSymbolandArguments(self.negate(sentence1))

            if predicateSymbol in predicatesDict:
                newSentence = self.substitute(predicateSymbol,arguments , predicatesDict[predicateSymbol], predicatesDict)
                if sentence2RepeatPred:
                    newSentence = self.getNormalSentenceForm(newSentence)

                return newSentence


        fusePredicateFound = False
        if "|" in sentence1 and len(predicatesDict) ==1 :

            predicatesList = sentence1.split("|")
            for index, predicate in enumerate(predicatesList):
                predicateSymbol, arguments = self.getPredicateSymbolandArguments(self.negate(predicate.strip()))
                normalpredicateSymbol, normalarguments = self.getPredicateSymbolandArguments(predicate.strip())

                if predicateSymbol not in predicatesDict:  # if Yes, then this is where we fuse these 2 predicateSymbols
                    if normalpredicateSymbol in predicatesDict:
                        return None

                    predicatesDict[normalpredicateSymbol] = normalarguments
                else:

                    if not fusePredicateFound:
                        fusePredicateFound = True
                        predicateSymbolLeft = predicateSymbol
                        argumentsLeft = arguments

                    else:
                        if normalpredicateSymbol in predicatesDict:
                            predicatesDict[normalpredicateSymbol+ "_" + str(self.KBDict[sentence1]) + "_" + str(index)]  =  normalarguments
                            sentence1RepeatPred = True
                        else:
                            predicatesDict[normalpredicateSymbol] = normalarguments


            newSentence = self.substitute(predicateSymbolLeft, argumentsLeft, predicatesDict[predicateSymbolLeft], predicatesDict)

            if sentence1RepeatPred:
                newSentence = self.getNormalSentenceForm(newSentence=newSentence)

            return newSentence


        if "|" in sentence1 and len(predicatesDict)>1:

            predicatesList = sentence1.split("|")
            for index, predicate in enumerate(predicatesList):
                predicateSymbol, arguments = self.getPredicateSymbolandArguments(self.negate(predicate.strip()))
                normalpredicateSymbol, normalarguments = self.getPredicateSymbolandArguments(predicate.strip())

                if predicateSymbol not in predicatesDict:  # if Yes, then this is where we fuse these 2 predicateSymbols
                    if normalpredicateSymbol in predicatesDict:
                        return None
                    predicatesDict[normalpredicateSymbol] = normalarguments
                else:

                    if not fusePredicateFound:
                        fusePredicateFound = True
                        predicateSymbolLeft = predicateSymbol
                        argumentsLeft = arguments

                    else:

                        predicatesDict[normalpredicateSymbol] = normalarguments
                        if normalpredicateSymbol in predicatesDict:
                            predicatesDict[normalpredicateSymbol + "_" + str(self.KBDict[sentence1]) + "_" + str(index)] = normalarguments

            newSentence = self.substitute(predicateSymbolLeft, argumentsLeft, predicatesDict[predicateSymbolLeft], predicatesDict)

            if newSentence == None:
                return None

            if "_" in newSentence:
                newSentence = self.getNormalSentenceForm(newSentence)

            return newSentence


    def getPredicateSymbolandArguments(self, predicate):
        """
        :param predicate: Takes in the predicate of some form eg: ~A, B, Father(x), Father(x,y), ~Father(x)  etc
        :return: predicateSymbol ~A, B, Father, Father, ~Father
        """

        openBracketIndex = re.search("\(", predicate).start()
        closeBracketIndex = re.search("\)", predicate).start()

        arguments = predicate[openBracketIndex+1 : closeBracketIndex]
        predicateSymbol = predicate[:openBracketIndex]

        # case1: multiple arguments were passed to the predicateSymbol i.e Father(x,y)
        # case2: we had a single argument i.e Father(x)
        # case3: we had no arguments at all ie ~B
        if "," in arguments:
            arguments = arguments.split(",")
        else:
            arguments = [arguments]

        return predicateSymbol, arguments

    def resolve(self, sentence1, sentence2):
        """

        :param sentence1:
        :param sentence2:
        :return:
         case 1: The sentence2 is a disjunction of literals
         case 2: The sentence2 is a single literal, ie literal = sentence2

        """

        if self.currentAns:
            return

        # stores the predicates in the form {"Father":[['x','y']], "~B:[[]], "Sister:"[['x'], ['z']], ..... }
        predicatesDict = {}
        sentence2_RepeatPred = False

        if "|" in sentence2:
            predicateList = [predicate.strip() for predicate in sentence2.split("|")]
            for index, predicate in enumerate(predicateList):
                predicateSymbol, arguments = self.getPredicateSymbolandArguments(predicate)
                arguments = [arg.strip() for arg in arguments]

                if predicateSymbol in predicatesDict:
                    predicatesDict[predicateSymbol+"_"+ str(self.KBDict[sentence2])+ "_" + str(index)] = arguments
                    sentence2_RepeatPred = True
                else:
                    predicatesDict[predicateSymbol] = arguments
        else:
            predicate = sentence2
            predicateSymbol, arguments = self.getPredicateSymbolandArguments(predicate)
            arguments = [arg.strip() for arg in arguments]
            predicatesDict[predicateSymbol] = arguments

        unifiedSentence = self.unify(sentence1, predicatesDict, sentence2_RepeatPred)

        # print("Unified Sentence:", unifiedSentence, "\n")

        # case2: unified the sentences and produced either {} or a new legit sentence or None
        if unifiedSentence == None:
            return None

        self.insertSentenceIntoKB(unifiedSentence)

        return unifiedSentence


    def getRelaventKBSubset(self, alpha):
        """
        :param alpha:
        :return:

         alpha could be of the form ~F(x) or ~C(John, x) | ~B(John,y), new to pick both in terms of C and B and not only C
        """

        if "|" in alpha:
            totalRelaventList = []
            predicateList = alpha.split("|")

            for predicate in predicateList:
                predicate = self.negate(predicate.strip())
                predicateSymbol1 = predicate.split("(")[0]
                if predicateSymbol1 in self.predicateSymbolsDict:
                    totalRelaventList+=self.predicateSymbolsDict[predicateSymbol1]

            if totalRelaventList:
                return totalRelaventList
            else:
                return None

        predicate =  self.negate(alpha)
        predicateSymbol1 = predicate.split("(")[0]


        if predicateSymbol1 in self.predicateSymbolsDict:
            return self.predicateSymbolsDict[predicateSymbol1]
        else:
            return None

    def resolutionAlgo(self, alpha):
        '''
        :param alpha: the current sentence we are operating upon, alpha is a part of KB. We get the list of sentences already in KB which could
         be paired with alpha to infer something new. If successful, add that new inference to the KB
        :return:
        '''
        if len(self.KB)>16000:
            return False

        if self.currentAns:
            return

        if alpha == None:
            return False

        if alpha in self.loopDetector:
            return False

        self.loopDetector[alpha] = len(self.loopDetector)

        if "{}" in self.KBDict:
            self.currentAns = True
            return False


        relevantKBSentenceIDList = self.getRelaventKBSubset(alpha)

        # case3: There is no way you can prove, given the KB we have
        if not relevantKBSentenceIDList:
            return False

        for relevantsentenceID in relevantKBSentenceIDList:
            newalpha = self.resolve(alpha, self.KB[relevantsentenceID])
            self.resolutionAlgo(newalpha)

        return self.currentAns

    def initCheck(self, negatedAsk):
        relevantKBSentenceIDList = self.getRelaventKBSubset(negatedAsk)
        if relevantKBSentenceIDList:
            return True
        else:
            return False


    def runInferrence(self):
        if not self.ask:
            return True

        for alpha in self.ask:
            # print("\n\n*************************************************")
            # print("Ask:", alpha)

            try:
                self.reInitValues()
                self.KB.insert(0, self.negate(alpha=alpha))

                self.preProcessKB()

                if self.initCheck(self.negate(alpha=alpha)):

                    for startState in self.KB:
                        boolYESNO = self.resolutionAlgo(startState)
                        if boolYESNO:
                            break
                else:
                    boolYESNO = False

                self.ans.append(boolYESNO)

            except Exception as e:
                self.ans.append(False)

        return self.ans


def main():

    logic = LogicEngine()
    logic.readData("input.txt")

    answerlist = logic.runInferrence()
    logic.writeOutput(answerlist)


if __name__ == "__main__":
    main()
