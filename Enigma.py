# ******************************************************************************************* #

#  Enigma.py

#  David Hoffmann
#  2018
#  GNU General Public License

#  Fun Python code to crack the WW2 German Enigma code, using similar method to the Turing Bombe machines,
#  adapted & modernised to run on current hardware.

#  Relies on a guessable crib word at the beginning of each message (eg. WETTERVORHERSAGEBISKAYA - 
#  German for weather report in the Biscay region, a regularly sent and intercepted message).
#  This followed the standard three letter message key (encrypted according to the universal day key).

#  From a single intercepted enciphered message the code obtains the enigma rotor types & positions, 
#  initial rotor settings and message key, even when chosen in line with proper procedure (unguessable). 
#  Note that for the slow rotor only the offset between initial orientation and ring setting is found, 
#  as the encryption is invariant to any initial rotation with this fixed offset.

#  Decryption of a second intercepted enciphered message, with a different message key but otherwise 
#  identical settings (no less general as >1 would certainly be intercepted per day!) allows for 
#  fast calculation of the day key: the final piece of the puzzle necessary for easy decryption of all 
#  messages that day.

#  I intend to write a more comprehensive explanation of the method used. Although it is based on the 
#  Turing Bomb machines, their workings are not at all well described in any literature that I could find.
#  A good deal of thought and retreading of old steps was required, although fortunately I had the 
#  advantage of knowing that in this approach a solution was there be found!

#  The code typically takes around 1-10 minutes on an average laptop for the first decription, dependent
#  on initial enigma settings. We have no choice but to take a fixed started point for the search, so if 
#  the slow rotor starts at the opposite end of the (wrapped) alphabet, then we will take much longer 
#  than at a letter or two ahead.  The second decription for the day key will take around 30 seconds.

#  Chance of slow rotor advance during crib is ~ crib length / 676, so for crib tests remove the possibility
#  of slow rotor advance. The code will fail if this does happen, but if slow rotor advance is permitted the 
#  code would fail 25 times out of 26 when "slow rotor offset" corresponds to a slow rotor notch value
#  (a far more common occurrence).

# ******************************************************************************************* #

from numpy import flipud
import string
from sys import exit, stdout
import time
from copy import deepcopy
import random
from operator import itemgetter
from itertools import permutations, product
from random import randint
from num2words import num2words
from math import log

# ****************************************************************** #

Find_Chain = 1                         # if 0 probably have manual input specified below
Early_Start = 3                        # if equal to non-zero Ns, seeks to find Chains with max Letter pos of first Ns Letters being no greater than the current Longest_Chain [perhaps have as a function of Guess length?]
Crack_Enigma = 1
Rotor_Repeats = 0                      # 0 forbids repeating same rotor in same slot day-to-day, 1 permits
Total_Steckers = 10                    # 0 for disabled, N for fixed N Stecker pairs
Adjacent_Steckers = 0                  # 0 for disallowed, 1 for allowed
Implied_Contradictions = 1             # contradictions rule out all relevant nnEO's 
Exit_If_Found = 1                      # exit after all Crib / Partial-Crib solutions for the given nr0, nr1 ,nr2
Print_Crib_Solutions = 0               # will always print if full solution not found
Print_Partial_Crib_Solutions = 0       # will always print if crib solution not found
Print_Erroneous_Crib_Solutions = 0     # will always print if partial crib solution not found
Print_Counts = 1
Calc_Day_Keys = 1
Print_Day_Keys = 0
Print_Day_Keys_and_Trials = 1

# ****************************************************************** #

# Functions

# Build a cost dictionary, assuming Zipf's law and cost = -math.log(probability).
words = open("Words-By-Frequency-English.txt").read().split()
wordcost = dict((k, log((i+1)*log(len(words)))) for i,k in enumerate(words))
maxword = max(len(x) for x in words)

def infer_spaces(s):
    """Uses dynamic programming to infer the location of spaces in a string
    without spaces."""

    # Find the best match for the i first characters, assuming cost has
    # been built for the i-1 first characters.
    # Returns a pair (match_cost, match_length).
    def best_match(i):
        candidates = enumerate(reversed(cost[max(0, i-maxword):i]))
        return min((c + wordcost.get(s[i-k-1:i], 9e999), k+1) for k,c in candidates)

    # Build the cost array.
    cost = [0]
    for i in range(1,len(s)+1):
        c,k = best_match(i)
        cost.append(c)
        
    # Backtrack to recover the minimal-cost string.
    out = []
    i = len(s)
    while i>0:
        c,k = best_match(i)
        assert c == cost[i]
        out.append(s[i-k:i])
        i -= k

    return " ".join(reversed(out))    

def Inverse(Alphabet):
    if len(Alphabet) != 26:
        print "Alphabet not correct length!\n"
        exit(1)
    else:
        Inverse_Alphabet = list('1'*26)
        for nl in range(26):
            Inverse_Alphabet[ord(Alphabet[nl])-65] = chr(nl+65)
    return Inverse_Alphabet
    
def Advance_Letter(Letter, number=1):
    if Letter.isupper():
        shift = 65
    else:
        shift = 97
    return chr((ord(Letter)-shift+number)%26 + shift) 
                
# ****************************************************************** #

# Classes

# Plugboard class
class Plugboard:
    def __init__(self, Stecker_List=[]): 
        self.Alphabet = list('ABCDEFGHIJKLMNOPQRSTUVWXYZ')
        self.Stecker_Pairs = []
        for Stecker in Stecker_List: 
            self.Alphabet[ord(Stecker[0])-65] = Stecker[1]
            self.Alphabet[ord(Stecker[1])-65] = Stecker[0]
            self.Stecker_Pairs += [sorted(Stecker)]
        self.Stecker_Pairs = sorted(self.Stecker_Pairs, key=itemgetter(0))
        
    def Reset_Plugboard(self, Stecker_List):
        self.Alphabet = list('ABCDEFGHIJKLMNOPQRSTUVWXYZ')
        self.Stecker_Pairs = []
        for Stecker in Stecker_List: 
            self.Alphabet[ord(Stecker[0])-65] = Stecker[1]
            self.Alphabet[ord(Stecker[1])-65] = Stecker[0]
            self.Stecker_Pairs += [sorted(Stecker)]
        self.Stecker_Pairs = sorted(self.Stecker_Pairs, key=itemgetter(0))
                    
    def Swap(self, input_Letter):
        output_Letter = self.Alphabet[ord(input_Letter.upper())-65]
        return output_Letter                  
                
# Rotor class
class Rotor:
    def __init__(self, Model, Rotation, Ring_Setting): 
        # Engima encryption rotors/wheels - from https://en.wikipedia.org/wiki/Enigma_rotor_details
        self.Model = Model
        if self.Model == 'I': 
            self.Alphabet = list('EKMFLGDQVZNTOWYHXUSPAIBRCJ')
            self.Notches = ['Q']
        elif self.Model == 'II': 
            self.Alphabet = list('AJDKSIRUXBLHWTMCQGZNPYFVOE')
            self.Notches = ['E']            
        elif self.Model == 'III': 
            self.Alphabet = list('BDFHJLCPRTXVZNYEIWGAKMUSQO')
            self.Notches = ['V']          
        elif self.Model == 'IV': 
            self.Alphabet = list('ESOVPZJAYQUIRHXLNFTGKDCMWB')
            self.Notches = ['J'] 
        elif self.Model == 'V': 
            self.Alphabet = list('VZBRGITYUPSDNHLXAWMJQOFECK')
            self.Notches = ['Z']             
        elif self.Model == 'VI': 
            self.Alphabet = list('JPGVOUMFYQBENHZRDKASXLICTW')
            self.Notches = ['Z','M']              
        elif self.Model == 'VII': 
            self.Alphabet = list('NZJHGRCXMYSWBOUFAIVLPEKQDT')
            self.Notches = ['Z','M']                 
        elif self.Model == 'VIII': 
            self.Alphabet = list('FKQHTLXOCBJSPDZRAMEWNIUYGV')
            self.Notches = ['Z','M']   
        self.Rotation = Rotation
        self.Ring_Setting = Ring_Setting   # Ring_Setting = ring settings (internal wiring offset vs rotor Alphabet ring & notches)
        self.inverse_Alphabet = Inverse(self.Alphabet)
    
    def Advance_Rotation(self):
        self.Rotation = Advance_Letter(self.Rotation)

    def Set_Rotation(self, Rotation):
        #self.Rotation = Rotation
        if isinstance(Rotation, str) == 1:
            self.Rotation = Rotation.upper()
        elif isinstance(Rotation, int) == 1:
            self.Rotation = chr(Rotation + 65)
        else:
            print "False type for input in Rotor.Set_Rotation! Exiting ..."
            exit(1)
            
    def Substitution(self, input_Letter):
        input_rotor = Advance_Letter(input_Letter, ord(self.Rotation)-65)
        input_wiring = Advance_Letter(input_rotor, -(ord(self.Ring_Setting)-65))
        output_wiring = self.Alphabet[ord(input_wiring)-65]
        output_wiring = Advance_Letter(output_wiring, ord(self.Ring_Setting)-65)
        output_rotor = Advance_Letter(output_wiring, -(ord(self.Rotation)-65))
        return output_rotor
        
    def Inverse_Substitution(self, input_Letter):
        input_rotor = Advance_Letter(input_Letter, ord(self.Rotation)-65)
        input_wiring = Advance_Letter(input_rotor, -(ord(self.Ring_Setting)-65))
        output_wiring = self.inverse_Alphabet[ord(input_wiring)-65]
        output_wiring = Advance_Letter(output_wiring, ord(self.Ring_Setting)-65)
        output_rotor = Advance_Letter(output_wiring, -(ord(self.Rotation)-65))
        return output_rotor    
          
# Reflector class
class Reflector:
    def __init__(self, Model):
        self.Model = Model
        if self.Model == 'B':  
            self.Alphabet = list('YRUHQSLDPXNGOKMIEBFZCWVJAT')
        elif self.Model == 'C':
            self.Alphabet = list('FVPJIAOYEDRZXWGCTKUQSBNMHL')
        elif self.Model == 'B_Thin':  
            self.Alphabet = list('ENKQAUYWJICOPBLMDXZVFTHRGS')
        elif self.Model == 'C_Thin':
            self.Alphabet = list('RDOBJNTKVEHMLFCWZAXGYIPSUQ')     

    def Reflection(self, input_Letter):
        output_Letter = self.Alphabet[ord(input_Letter)-65]
        return output_Letter
        
# Enigma Class
class Enigma:
    def __init__(self, PB, Rotors, Rfl):
        self.PB = PB
        self.Rotors = Rotors   # Rotors in order of use (ie. right to left)
        self.Rfl = Rfl           

    def Switch_Plugboard(self, PB):
        self.PB = PB
    
    def Set_Rotor_Rotations(self, Rotations):
        for nR in range(len(self.Rotors)):
            self.Rotors[nR].Rotation = Rotations[nR]

    def Set_Ring_Settings(self, Ring_Settings):
        for nR in range(len(self.Rotors)):
            self.Rotors[nR].Ring_Setting = Ring_Settings[nR]
                
    def Advance_Rotors(self, Na=1):
        for na in range(Na):
            Advance_Rotations = [0]*len(self.Rotors)
            Advance_Rotations[0] = 1
            for nR in range(1, len(self.Rotors)):
                for Notch in self.Rotors[nR-1].Notches:
                    if (ord(self.Rotors[nR-1].Rotation)-ord(Notch))%26 == 0:  
                        Advance_Rotations[nR] = 1
                        break
            # Single-step check                           
            for nR in range(len(self.Rotors)):
                if Advance_Rotations[nR] == 1:
                    self.Rotors[nR].Rotation = Advance_Letter(self.Rotors[nR].Rotation)
            # Double-step check
            for nR in range(1, len(self.Rotors)-1):
                if Advance_Rotations[nR+1] == 1:
                    self.Rotors[nR].Rotation = Advance_Letter(self.Rotors[nR].Rotation) 

    def Advance_Rotors_No_Slow(self, Na=1):
        for na in range(Na):
            Advance_Rotations = [0]*len(self.Rotors)
            Advance_Rotations[0] = 1
            for Notch in self.Rotors[0].Notches:
                if (ord(self.Rotors[0].Rotation)-ord(Notch))%26 == 0:  
                    Advance_Rotations[1] = 1
                    break
            # Single-step check                           
            for nR in range(len(self.Rotors)):
                if Advance_Rotations[nR] == 1:
                    self.Rotors[nR].Rotation = Advance_Letter(self.Rotors[nR].Rotation)

    def Scrambler(self, Letter_Input):
        Letter_Rotors = Letter_Input
        for Rtr in self.Rotors:
            Letter_Rotors = Rtr.Substitution(Letter_Rotors)
        Letter_Reflector = self.Rfl.Reflection(Letter_Rotors)
        Letter_Rotors = Letter_Reflector  
        for Rtr in flipud(self.Rotors):          
            Letter_Rotors = Rtr.Inverse_Substitution(Letter_Rotors)
        Letter_Output = Letter_Rotors      
        return Letter_Output
     
    def Encipher_Message(self, Message_Input, Print_All=0):
        Message_Input = Message_Input.translate(None, string.punctuation)
        Message_Output = ""
        for nl in range(len(Message_Input)):
            Letter_Input = Message_Input[nl] 
            if type(Letter_Input) is str and Letter_Input != ' ': 
                # Mechanical part
                self.Advance_Rotors()
                # Electrical part
                Letter_Output = self.PB.Swap(Letter_Input)                
                Letter_Output = self.Scrambler(Letter_Output)
                Letter_Output = self.PB.Swap(Letter_Output)  
                Message_Output += Letter_Output 
                if Print_All == 1:
                    print [self.Rotors[0].Rotation, self.Rotors[1].Rotation, self.Rotors[2].Rotation], Letter_Input, Letter_Output
        return Message_Output

    def Encipher_Message_and_Restore(self, Message_Input, Print_All=0):
        Rotations_Copy = deepcopy([self.Rotors[0].Rotation, self.Rotors[1].Rotation, self.Rotors[2].Rotation])        
        Message_Output = self.Encipher_Message(Message_Input, Print_All)
        [self.Rotors[0].Rotation, self.Rotors[1].Rotation, self.Rotors[2].Rotation] = deepcopy(Rotations_Copy)
        return Message_Output        

    def Encipher_Message_No_Slow(self, Message_Input, Print_All=0):
        Message_Input = Message_Input.translate(None, string.punctuation)
        Message_Output = ""
        for nl in range(len(Message_Input)):
            Letter_Input = Message_Input[nl] 
            if type(Letter_Input) is str and Letter_Input != ' ': 
                # Mechanical part
                self.Advance_Rotors_No_Slow()
                # Electrical part
                Letter_Output = self.PB.Swap(Letter_Input)                
                Letter_Output = self.Scrambler(Letter_Output)
                Letter_Output = self.PB.Swap(Letter_Output)  
                Message_Output += Letter_Output 
                if Print_All == 1:
                    print [self.Rotors[0].Rotation, self.Rotors[1].Rotation, self.Rotors[2].Rotation], Letter_Input, Letter_Output
        return Message_Output

    def Encipher_Message_and_Restore_No_Slow(self, Message_Input, Print_All=0):
        Rotations_Copy = deepcopy([self.Rotors[0].Rotation, self.Rotors[1].Rotation, self.Rotors[2].Rotation])        
        Message_Output = self.Encipher_Message_No_Slow(Message_Input, Print_All)
        [self.Rotors[0].Rotation, self.Rotors[1].Rotation, self.Rotors[2].Rotation] = deepcopy(Rotations_Copy)
        return Message_Output   
                                                        
    def Number_of_Steps(self, Target, Initial_Rotations=[]):
        Rotations_Copy = deepcopy([self.Rotors[0].Rotation, self.Rotors[1].Rotation, self.Rotors[2].Rotation])        
        if Initial_Rotations == []:
            Initial_Rotations = deepcopy([self.Rotors[0].Rotation, self.Rotors[1].Rotation, self.Rotors[2].Rotation])      
        Nsteps = 0
        if Target == "Middle Rotor Advance":
            while self.Rotors[1].Rotation == Initial_Rotations[1]:        
                self.Advance_Rotors()
                Nsteps += 1            
        elif Target == "Slow Rotor Advance":
            while self.Rotors[2].Rotation == Initial_Rotations[2]:        
                self.Advance_Rotors()
                Nsteps += 1                  
        else:
            while [self.Rotors[0].Rotation, self.Rotors[1].Rotation, self.Rotors[2].Rotation] != Target:
                self.Advance_Rotors()
                Nsteps += 1
        [self.Rotors[0].Rotation, self.Rotors[1].Rotation, self.Rotors[2].Rotation] = deepcopy(Rotations_Copy) 
        return Nsteps


# ****************************************************************** #
                                
def Find_Longest_Chain(Crib_Ciphertext, Crib_Guess, Early_Start):
   
    Letters = {}
    for nl in range(len(Crib_Guess)):
        if Crib_Guess[nl] in Letters:
            Letters[Crib_Guess[nl]].append(nl)
        else:
            Letters[Crib_Guess[nl]] = [nl]          
        if Crib_Ciphertext[nl] in Letters:
            Letters[Crib_Ciphertext[nl]].append(nl)   
        else:
            Letters[Crib_Ciphertext[nl]] = [nl]
    
    Links = {}
    for Letter in Letters:
        Link = []
        for nlp in range(len(Crib_Guess)):
            if Crib_Guess[nlp] == Letter[0]:
                Link += [[Crib_Ciphertext[nlp], nlp]]
            elif Crib_Ciphertext[nlp] == Letter[0]:
                Link += [[Crib_Guess[nlp], nlp]]
        Links[Letter[0]] = Link
        
    # from random starting points randomly choose path until no more possible paths, then find the longest chain
    Ntrial = 1000
    Longest_Chain = ''
    while len(Longest_Chain) < 10:                                   
        Longest_Chain = [['A',999], ['B',999]] #[]  
        Longest_Chain_Length = 0
        for ntrial in range(Ntrial): 
            Links_copy = deepcopy(Links)
            Letter = [random.choice(Links_copy.keys()) , -1]
            Trial_Chain = [Letter] 
            while len(Links_copy[Letter[0]]) > 0:
                next_Letter = random.choice(Links_copy[Letter[0]])
                Trial_Chain += [next_Letter]    
                Links_copy[Letter[0]].remove(next_Letter)
                Links_copy[next_Letter[0]].remove([Letter[0], next_Letter[1]])
                Letter = next_Letter     
            for Letter in list(set([Letter2[0] for Letter2 in Trial_Chain])):  # remove duplicates
                if (Early_Start > 0) and (len(Trial_Chain) >= Longest_Chain_Length) and (max([Letter3[1] for Letter3 in Trial_Chain[1:Early_Start+1]]) <= max([Letter3[1] for Letter3 in Longest_Chain[1:Early_Start+1]])):            
                    Longest_Chain_Length = len(Trial_Chain)
                    Longest_Chain = deepcopy(Trial_Chain)  
                elif (Early_Start == 0) and (len(Trial_Chain) > Longest_Chain_Length):
                    Longest_Chain_Length = len(Trial_Chain)
                    Longest_Chain = deepcopy(Trial_Chain)
        Early_Start -= 1   
        
    return Longest_Chain   
    

def Crack_Enigma_AN3(Message_Ciphertext, Message_Plaintext, Crib_Guess, Longest_Chain, Rotor_Repeats, Rotors_Yesterday, Nstc, Adjacent_Steckers, Implied_Contradictions, Exit_If_Found):
    
    Alphabet = list('ABCDEFGHIJKLMNOPQRSTUVWXYZ')
    Crib_Ciphertext = Message_Ciphertext[:len(Crib_Guess)]
    NE = len(Longest_Chain) - 1      
        
    # Store (reverse) order of application of the enigmas in the Message
    nE_Order = [E[0] for E in sorted(zip(range(len(Longest_Chain)-1), [Letter[1] for Letter in Longest_Chain[1:]]), key=itemgetter(1))]
    nE_RevOrder = flipud(nE_Order)      
    
    nnE_Cont = [0]*NE
    for nE in range(NE):
        nnE_Cont[nE] = 0
        for nE2 in [n for n in range(NE) if n!=nE]:
            if Longest_Chain[nE2+1][1] > max([l[1] for l in Longest_Chain[1:nE+2]]):
                nnE_Cont[nE] += 1   

    #print "nE_RevOrder =", nE_RevOrder
                
    Possible_Notches = [0]*(NE+1)
    nls_known = [0]*(NE+1)
    for nnEO in range(NE+1):            
        if nnEO == 0:
            Possible_Notches[nnEO] = range(Longest_Chain[nE_RevOrder[nnEO]+1][1]+1, 26)
            nls_known[nnEO] = range(Longest_Chain[nE_RevOrder[nnEO]+1][1]+1)
        elif nnEO == NE:
            Possible_Notches[nnEO] = range(Longest_Chain[nE_RevOrder[0]+1][1]+1 - 26, Longest_Chain[nE_RevOrder[NE-1]+1][1]+1)
            #nls_known[nnEO] = range(Longest_Chain[nE_RevOrder[NE-1]+1][1]+1, len(Crib_Ciphertext))
            nls_known[nnEO] = range(Longest_Chain[nE_RevOrder[NE-1]+1][1], len(Crib_Ciphertext))
            #nls_known[nnEO] = range(len(Crib_Ciphertext))
            
        else:
            Possible_Notches[nnEO] = range(Longest_Chain[nE_RevOrder[nnEO]+1][1]+1, Longest_Chain[nE_RevOrder[nnEO-1]+1][1]+1)
            nls_known[nnEO] = range(Longest_Chain[nE_RevOrder[nnEO]+1][1]+1)+range(Longest_Chain[nE_RevOrder[nnEO-1]+1][1], len(Crib_Ciphertext))

    #print "nls_known =", nls_known

    if Adjacent_Steckers == 0:
        Scrambler_Inputs = [Letter for Letter in Alphabet if ((chr(ord(Letter)+1) != Longest_Chain[0][0]) and (chr(ord(Letter)-1) != Longest_Chain[0][0]))]
    else:
        Scrambler_Inputs = Alphabet
    
    Rotor_List = ['I', 'II', 'III', 'IV', 'V', 'VI', 'VII', 'VIII']
    NR = 3
    Rotor_List = Rotor_List[:NR]
    if Rotor_Repeats == 0:
        Rotor_Perms = [Rotor_Perm for Rotor_Perm in list(permutations(Rotor_List,3)) if (Rotor_Perm[0]!=Rotors_Yesterday[0] and Rotor_Perm[1]!=Rotors_Yesterday[1] and Rotor_Perm[2]!=Rotors_Yesterday[2])]
    else:
        Rotor_Perms = list(permutations(Rotor_List,3))  
    
    Count_Rotations = 0
    Count_Scrambler_Letters = 0
    Count_Scrambler_Notches = 0
    Count_Valid_Paths = 0    
    Count_Valid_Cribs = 0 
    Count_NmX_Steckers = [0]*Nstc 
    Erroneous_Crib_Solutions = []
    Partial_Crib_Solutions = []
    Crib_Solutions = [] 
    Full_Solutions = [] 
    Counts = []
    Countdown = "Inactive"
          
    print "\nStall count: " #,  
   
    for Rotor_Models in Rotor_Perms:
    #for Rotor_Models in [['III', 'II', 'I']]:

        print [Rotor_Models[0], Rotor_Models[1], Rotor_Models[2]],  
        Stalls = 0
        
        # Enigma initial configuration
        Rotations = ['A', 'A', 'A']
        Ring_Settings = ['A', 'A', 'A']        
        PB_Null = Plugboard() 
        Rotors = []
        for nR in range(len(Rotor_Models)):
            Rotors += [Rotor(Rotor_Models[nR], Rotations[nR], Ring_Settings[nR])]
        Rfl = Reflector('B')                 

        # Create loop of Enigma machines 
        Enigma_Chain = []
        for nE in range(NE):
            # Army / Navy 3 rotor enigma 
            Enigma_AN3 = Enigma(PB_Null, deepcopy(Rotors), Rfl)             
            # Set fast rotor Rotation without "Notching on" - for pairwise substitution (after rotor step on: so +1)
            Enigma_AN3.Set_Rotor_Rotations([Advance_Letter(Rotations[0], Longest_Chain[nE+1][1]+1), Rotations[1], Rotations[2]])                                                   
            Enigma_Chain += [Enigma_AN3]

        Enigma_Start = Enigma(PB_Null, deepcopy(Rotors), Rfl)    # Initial settings (ie. before rotor step on)
        Enigma_Tester = Enigma(PB_Null, deepcopy(Rotors), Rfl)   
        
        Nr0 = 26    # fast rotor
        Nr1 = 26    # middle rotor
        Nr2 = 26    # slow rotor
        nrs2 = range(ord(Rotations[2])-65,min(ord(Rotations[2])-65+Nr2,26))+range(ord(Rotations[2])-65-26+Nr2)
        nrs1 = range(ord(Rotations[1])-65,min(ord(Rotations[1])-65+Nr1,26))+range(ord(Rotations[1])-65-26+Nr1)
        nrs0 = range(ord(Rotations[0])-65,min(ord(Rotations[0])-65+Nr0,26))+range(ord(Rotations[0])-65-26+Nr0)

        # Number of possible initial Rotations on each of the three rotors
        for nr2 in nrs2:
            if type(Countdown) is int:
                Countdown -= 1  
            for nr1 in nrs1:
                for nr0 in nrs0:  

                    Count_Rotations += 1                                                                                                                                                                                               
                    for Scrambler_Input in Scrambler_Inputs:  # for each possible Letter input into the scramber chain               
                        nnEO = 0
                        nnE_adv = 1
                        Count_Scrambler_Letters +=1 
                        while nnEO <= NE:  # check possible Notch positions (middle rotors advanced for enigmas in reverse Letter position order)                       
                            # Find possible routes through scrambler chain (ie. no contradictions) and necessary steckers                                                                                                                                                                                                                                                                                                                                                              
                            Count_Scrambler_Notches += 1
                            Scrambler_Route = [Scrambler_Input] 
                            Stecker_Path_Valid = 1
                            if Scrambler_Input == Longest_Chain[0][0]:
                                Stecker_List_Base = []
                                Stecker_Pairs_Base = []                            
                                Unsteckered_Base = [Scrambler_Input]    
                            else:
                                Stecker_List_Base = sorted([Longest_Chain[0][0], Scrambler_Input])
                                Stecker_Pairs_Base = [sorted([Longest_Chain[0][0], Scrambler_Input])]
                                Unsteckered_Base = []
                                
                            for nE in range(NE):  
                                Letter = Enigma_Chain[nE].Scrambler(Scrambler_Route[nE])
                                if Letter == Longest_Chain[nE+1][0]:  # If scrambler output equal to (scrambler + plugboard) output
                                    if Letter in Stecker_List_Base: # Or Longest_Chain[nE+1][0] in Stecker_List[0] is redundant since equal
                                        Stecker_Path_Valid = 0 # Contradiction: Letter already steckered but need unsteckered
                                        break
                                    elif Letter not in Unsteckered_Base:
                                        Unsteckered_Base += [Letter]    
                                else:
                                    if (Letter in Stecker_List_Base) or (Longest_Chain[nE+1][0] in Stecker_List_Base):                                                          
                                        if sorted([Letter, Longest_Chain[nE+1][0]]) not in Stecker_Pairs_Base:     
                                            Stecker_Path_Valid = 0 # Contradiction: Letter from scrambler already steckered to different Letter 
                                            break                                                         
                                    elif (Letter in Unsteckered_Base) or (Longest_Chain[nE+1][0] in Unsteckered_Base):
                                        Stecker_Path_Valid = 0 # Contradiction: need to stecker but would lead to contradiction
                                        break    
                                    elif (Adjacent_Steckers == 0) and ((chr(ord(Letter)+1) == Longest_Chain[nE+1][0]) or (chr(ord(Letter)-1) == Longest_Chain[nE+1][0])):
                                        Stecker_Path_Valid = 0 # Contradiction: no adjacent steckers
                                        break                                     
                                    else:    
                                        Stecker_List_Base += sorted([Letter, Longest_Chain[nE+1][0]])
                                        Stecker_Pairs_Base += [sorted([Letter, Longest_Chain[nE+1][0]])]                                                               
                                Scrambler_Route += [Letter]                                                                                                                 
                                                                                                                                                                                    
                            # For valid routes + steckers through scrambler chain, check full Crib_Deciphered against Crib_Plaintext to obtain more steckers
                            if Stecker_Path_Valid == 1: 

                                Count_Valid_Paths += 1                                                                                                                                                                                                  
                                Stecker_Pairs_Base = sorted(Stecker_Pairs_Base, key=itemgetter(0))
                                Notch_Offset = (-(ord(Enigma_Start.Rotors[0].Rotation)-65) + ord(Enigma_Start.Rotors[0].Notches[0])-65 - Possible_Notches[nnEO][-1])%26  # select latest possible Notch position (so can later loop over Alphabet in forward direction)
                                Enigma_Tester.Switch_Plugboard(Plugboard(Stecker_Pairs_Base)) 
                                Enigma_Tester.Set_Ring_Settings([Advance_Letter(Enigma_Start.Rotors[0].Ring_Setting, Notch_Offset), Enigma_Start.Rotors[1].Ring_Setting, Enigma_Start.Rotors[2].Ring_Setting])                    
                                Enigma_Tester.Set_Rotor_Rotations([Advance_Letter(Enigma_Start.Rotors[0].Rotation, Notch_Offset), Enigma_Start.Rotors[1].Rotation, Enigma_Start.Rotors[2].Rotation])
                                Crib_Deciphered = Enigma_Tester.Encipher_Message_and_Restore_No_Slow(Crib_Ciphertext)
                                Crib_Enciphered = Enigma_Tester.Encipher_Message_and_Restore_No_Slow(Crib_Guess) 

                                Stecker_search = 1
                                while Stecker_search == 1:
                                    Crib_Deciphered_old = Crib_Deciphered

                                    for nlk in nls_known[nnEO]:      
                                        Steckers_change = 0
                                        Unsteckered_change = 0
                                        
                                        # What if match by chance with erroneous settings? Then will discover & reject later.
                                        if Crib_Deciphered[nlk] == Crib_Guess[nlk]:
                                            if (Crib_Ciphertext[nlk] in Stecker_List_Base) and (Crib_Deciphered[nlk] not in Stecker_List_Base)  and (Crib_Deciphered[nlk] not in Unsteckered_Base):                                            
                                                Unsteckered_Base += [Crib_Deciphered[nlk]] 
                                                Unsteckered_change = 1
                                            elif (Crib_Deciphered[nlk] in Stecker_List_Base) and (Crib_Ciphertext[nlk] not in Stecker_List_Base)  and (Crib_Ciphertext[nlk] not in Unsteckered_Base):                                            
                                                Unsteckered_Base += [Crib_Ciphertext[nlk]] 
                                                Unsteckered_change = 1
                                                
                                        elif (Crib_Ciphertext[nlk] in Stecker_List_Base) or (Crib_Ciphertext[nlk] in Unsteckered_Base):
                                            if (Crib_Deciphered[nlk] in Stecker_List_Base) or (Crib_Deciphered[nlk] in Unsteckered_Base):                                         
                                                Stecker_search = 0
                                                Stecker_Path_Valid = 0 # Contradiction: Letter already steckered to different Letter / shown as unsteckered 
                                                break  
                                            elif (Crib_Guess[nlk] in Stecker_List_Base) or (Crib_Guess[nlk] in Unsteckered_Base):                                              
                                                Stecker_search = 0
                                                Stecker_Path_Valid = 0 # Contradiction: Letter already steckered to different Letter / shown as unsteckered 
                                                break    
                                            elif (Adjacent_Steckers == 0) and ((chr(ord(Crib_Deciphered[nlk])+1) == Crib_Guess[nlk]) or (chr(ord(Crib_Deciphered[nlk])-1) == Crib_Guess[nlk])):
                                                Stecker_search = 0
                                                Stecker_Path_Valid = 0 # Contradiction: no adjacent steckers
                                                break                                                                                                                                 
                                            else:
                                                Stecker_List_Base += sorted([Crib_Deciphered[nlk], Crib_Guess[nlk]])
                                                Stecker_Pairs_Base += [sorted([Crib_Deciphered[nlk], Crib_Guess[nlk]])]
                                                Steckers_change = 1
                                                
                                        elif (Crib_Guess[nlk] in Stecker_List_Base) or (Crib_Guess[nlk] in Unsteckered_Base):
                                            if (Crib_Enciphered[nlk] in Stecker_List_Base) or (Crib_Enciphered[nlk] in Unsteckered_Base):                                         
                                                Stecker_search = 0
                                                Stecker_Path_Valid = 0 # Contradiction: Letter already steckered to different Letter / shown as unsteckered 
                                                break 
                                            elif (Adjacent_Steckers == 0) and ((chr(ord(Crib_Enciphered[nlk])+1) == Crib_Ciphertext[nlk]) or (chr(ord(Crib_Enciphered[nlk])-1) == Crib_Ciphertext[nlk])):
                                                Stecker_search = 0
                                                Stecker_Path_Valid = 0 # Contradiction: no adjacent steckers
                                                break                                                                                
                                            else:
                                                Stecker_List_Base += sorted([Crib_Enciphered[nlk], Crib_Ciphertext[nlk]])                                              
                                                Stecker_Pairs_Base += [sorted([Crib_Enciphered[nlk], Crib_Ciphertext[nlk]])]
                                                Steckers_change = 1 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             
                                        if Steckers_change == 1:
                                            Enigma_Tester.Switch_Plugboard(Plugboard(Stecker_Pairs_Base))         
                                            Enigma_Tester.Set_Rotor_Rotations([Advance_Letter(Enigma_Start.Rotors[0].Rotation, Notch_Offset), Enigma_Start.Rotors[1].Rotation, Enigma_Start.Rotors[2].Rotation])
                                            Crib_Deciphered = Enigma_Tester.Encipher_Message_and_Restore_No_Slow(Crib_Ciphertext) 
                                            Crib_Enciphered = Enigma_Tester.Encipher_Message_and_Restore_No_Slow(Crib_Guess)                                                      
                                            break
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                
                                    Stecker_Pairs_Base = sorted(Stecker_Pairs_Base, key=itemgetter(0))                          
                                                                                                    
                                    Letters_match = ['-']*26 
                                    for nlk in nls_known[nnEO]:
                                        if Crib_Deciphered[nlk] != Crib_Guess[nlk]:
                                            Letters_match[nlk] = 0
                                        else:
                                            Letters_match[nlk] = 1
                                    if 0 not in Letters_match:
                                        break
                                    if (Crib_Deciphered == Crib_Deciphered_old) and (Unsteckered_change == 0):
                                        break  

                                if (Stecker_Path_Valid == 1):
                                                                                                                                                                                                                                                                                                             
                                    nlp_soln = []
                                    nl_possible = flipud(Possible_Notches[nnEO])
                                                                        
                                    for nlp in nl_possible:   
                                                                               
                                        Stecker_List_Notch = deepcopy(Stecker_List_Base) 
                                        Stecker_Pairs_Notch = deepcopy(Stecker_Pairs_Base) 
                                        Unsteckered_Notch = deepcopy(Unsteckered_Base)  
                                        Enigma_Tester.Switch_Plugboard(Plugboard(Stecker_Pairs_Notch))
                                                                
                                        Notch_Offset = (-(ord(Enigma_Start.Rotors[0].Rotation)-65) + ord(Enigma_Start.Rotors[0].Notches[0])-65 - nl_possible[0])%26  
                                        Enigma_Tester.Set_Ring_Settings([Advance_Letter(Enigma_Start.Rotors[0].Ring_Setting, Notch_Offset), Enigma_Start.Rotors[1].Ring_Setting, Enigma_Start.Rotors[2].Ring_Setting])                                                      
                                        Enigma_Tester.Set_Rotor_Rotations([Advance_Letter(Enigma_Start.Rotors[0].Rotation, Notch_Offset), Enigma_Start.Rotors[1].Rotation, Enigma_Start.Rotors[2].Rotation])
                                        Enigma_Tester.Rotors[0].Ring_Setting = Advance_Letter(Enigma_Tester.Rotors[0].Ring_Setting, nl_possible[0]-nlp)   
                                        Enigma_Tester.Advance_Rotors_No_Slow(nl_possible[0]-nlp)                                        
                                        if Enigma_Tester.Rotors[1].Rotation in Enigma_Tester.Rotors[1].Notches:
                                            Enigma_Tester.Rotors[1].Rotation = Advance_Letter(Enigma_Tester.Rotors[1].Rotation)
                                            Enigma_Tester.Rotors[1].Ring_Setting = Advance_Letter(Enigma_Tester.Rotors[1].Ring_Setting)    
        
                                        Ring_Settings_Test = [Enigma_Tester.Rotors[0].Ring_Setting, Enigma_Tester.Rotors[1].Ring_Setting, Enigma_Tester.Rotors[2].Ring_Setting]
                                        Rotations_Test = [Enigma_Tester.Rotors[0].Rotation, Enigma_Tester.Rotors[1].Rotation, Enigma_Tester.Rotors[2].Rotation]                                               
                                        Crib_Deciphered = Enigma_Tester.Encipher_Message_and_Restore_No_Slow(Crib_Ciphertext)
                                        Crib_Enciphered = Enigma_Tester.Encipher_Message_and_Restore_No_Slow(Crib_Guess)   
                                                                                    
                                        Stecker_search = 1
                                        while Stecker_search == 1:
                                            Crib_Deciphered_old = Crib_Deciphered
                                            for nla in range(len(Crib_Guess)):      
                                                Steckers_change = 0
                                                Unsteckered_change = 0
                                                # What if match by chance with erroneous settings? Then will discover & reject later.
                                                if Crib_Deciphered[nla] == Crib_Guess[nla]:
                                                    if (Crib_Ciphertext[nla] in Stecker_List_Notch) and (Crib_Deciphered[nla] not in Stecker_List_Notch)  and (Crib_Deciphered[nla] not in Unsteckered_Notch):                                            
                                                        Unsteckered_Notch += [Crib_Deciphered[nla]] 
                                                        Unsteckered_change = 1
                                                    elif (Crib_Deciphered[nla] in Stecker_List_Notch) and (Crib_Ciphertext[nla] not in Stecker_List_Notch)  and (Crib_Ciphertext[nla] not in Unsteckered_Notch):                                            
                                                        Unsteckered_Notch += [Crib_Ciphertext[nla]] 
                                                        Unsteckered_change = 1

                                                elif (Crib_Ciphertext[nla] in Stecker_List_Notch) or (Crib_Ciphertext[nla] in Unsteckered_Notch):
                                                    if (Crib_Deciphered[nla] in Stecker_List_Notch) or (Crib_Deciphered[nla] in Unsteckered_Notch):                                         
                                                        Stecker_search = 0
                                                        Stecker_Path_Valid = 0 # Contradiction: Letter already steckered to different Letter / shown as unsteckered 
                                                        break  
                                                    elif (Crib_Guess[nla] in Stecker_List_Notch) or (Crib_Guess[nla] in Unsteckered_Notch):                                              
                                                        Stecker_search = 0
                                                        Stecker_Path_Valid = 0 # Contradiction: Letter already steckered to different Letter / shown as unsteckered 
                                                        break    
                                                    elif (Adjacent_Steckers == 0) and ((chr(ord(Crib_Deciphered[nla])+1) == Crib_Guess[nla]) or (chr(ord(Crib_Deciphered[nla])-1) == Crib_Guess[nla])):
                                                        Stecker_search = 0
                                                        Stecker_Path_Valid = 0 # Contradiction: no adjacent steckers
                                                        break                                                                                                                                 
                                                    else:
                                                        Stecker_List_Notch += sorted([Crib_Deciphered[nla], Crib_Guess[nla]])
                                                        Stecker_Pairs_Notch += [sorted([Crib_Deciphered[nla], Crib_Guess[nla]])]
                                                        Steckers_change = 1
                                                        
                                                elif (Crib_Guess[nla] in Stecker_List_Notch) or (Crib_Guess[nla] in Unsteckered_Notch):
                                                    if (Crib_Enciphered[nla] in Stecker_List_Notch) or (Crib_Enciphered[nla] in Unsteckered_Notch):                                         
                                                        Stecker_search = 0
                                                        Stecker_Path_Valid = 0 # Contradiction: Letter already steckered to different Letter / shown as unsteckered 
                                                        break 
                                                    elif (Adjacent_Steckers == 0) and ((chr(ord(Crib_Enciphered[nla])+1) == Crib_Ciphertext[nla]) or (chr(ord(Crib_Enciphered[nla])-1) == Crib_Ciphertext[nla])):
                                                        Stecker_search = 0
                                                        Stecker_Path_Valid = 0 # Contradiction: no adjacent steckers
                                                        break                                                                                
                                                    else:
                                                        Stecker_List_Notch += sorted([Crib_Enciphered[nla], Crib_Ciphertext[nla]])                                              
                                                        Stecker_Pairs_Notch += [sorted([Crib_Enciphered[nla], Crib_Ciphertext[nla]])]
                                                        Steckers_change = 1 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    
                                                if Steckers_change == 1:
                                                    Enigma_Tester.Switch_Plugboard(Plugboard(Stecker_Pairs_Notch))         
                                                    Crib_Deciphered = Enigma_Tester.Encipher_Message_and_Restore_No_Slow(Crib_Ciphertext) 
                                                    Crib_Enciphered = Enigma_Tester.Encipher_Message_and_Restore_No_Slow(Crib_Guess)                                                      
                                                    break 
                                                    
                                            Stecker_Pairs_Notch = sorted(Stecker_Pairs_Notch, key=itemgetter(0))  
                                                                                                                                                                                                                                       
                                            Letters_match = ['-']*26 
                                            for nlk in nls_known[nnEO]:
                                                if Crib_Deciphered[nlk] != Crib_Guess[nlk]:
                                                    Letters_match[nlk] = 0
                                                else:
                                                    Letters_match[nlk] = 1
                                            if 0 not in Letters_match:
                                                break
                                            if (Crib_Deciphered == Crib_Deciphered_old) and (Unsteckered_change == 0):
                                                break                                                                                                                         
    
                                        nls_mismatch = []
                                        for nlk in range(len(Crib_Guess)):
                                            if Crib_Deciphered[nlk] != Crib_Guess[nlk]: 
                                                nls_mismatch += [nlk]

                                        if len(nls_mismatch) == 0:  
                                            Stecker_List_Solutions = [[]]
                                            Stecker_Pairs_Solutions = [[]]
                                            Unsteckered_Solutions = [[]]

                                        else:  
                                                
                                            Promising_Double_Stecker_Pairs = []
                                            for nlmm in nls_mismatch: 
                                                Promising_Double_Stecker_Pairs += [[nlmm, []]]       
                                                if Adjacent_Steckers == 0:
                                                    Possible_Steckers = [letter for letter in Alphabet if (letter not in Stecker_List_Notch) and (letter not in Unsteckered_Notch) and (letter!=Crib_Ciphertext[nlmm]) and (ord(letter)!=ord(Crib_Ciphertext[nlmm])-1) and (ord(letter)!=ord(Crib_Ciphertext[nlmm])+1)]                                            
                                                else:
                                                    Possible_Steckers = [letter for letter in Alphabet if (letter not in Stecker_List_Notch) and (letter not in Unsteckered_Notch) and (letter!=Crib_Ciphertext[nlmm])]                                        

                                                Crib_Deciphered_Trial = Enigma_Tester.Encipher_Message_and_Restore_No_Slow(Crib_Ciphertext)

                                                if (Crib_Ciphertext[nlmm] not in Stecker_List_Notch) and ((Crib_Deciphered_Trial[nlmm] not in Stecker_List_Notch and Crib_Guess[nlmm] not in Stecker_List_Notch) or sorted([Crib_Deciphered_Trial[nlmm], Crib_Guess[nlmm]]) in Stecker_Pairs_Notch) and Crib_Deciphered_Trial[nlmm] not in Unsteckered_Notch and Crib_Guess[nlmm] not in Unsteckered_Notch:                                                
                                                    Promising_Double_Stecker_Pairs[-1][1] += [[[Crib_Ciphertext[nlmm], 'Unsteckered'], sorted([Crib_Deciphered_Trial[nlmm], Crib_Guess[nlmm]])]]     
                                                    
                                                for Stecker in Possible_Steckers:
                                                    Stecker_Pairs_Trial = Stecker_Pairs_Notch + [sorted([Crib_Ciphertext[nlmm], Stecker])]
                                                    Enigma_Tester.Switch_Plugboard(Plugboard(Stecker_Pairs_Trial))         
                                                    Crib_Deciphered_Trial = Enigma_Tester.Encipher_Message_and_Restore_No_Slow(Crib_Ciphertext) 
                                                
                                                    if Crib_Deciphered_Trial[nlmm] == Crib_Guess[nlmm] and ((Crib_Ciphertext[nlmm] not in Stecker_List_Notch and Stecker not in Stecker_List_Notch) or sorted([Crib_Ciphertext[nlmm], Stecker]) in Stecker_Pairs_Notch) and Crib_Ciphertext[nlmm] not in Unsteckered_Notch and Stecker not in Unsteckered_Notch:                                                                                                
                                                        if Crib_Deciphered_Trial[nlmm] in Stecker_List_Notch:
                                                            nind = Stecker_List_Notch.index(Crib_Deciphered_Trial[nlmm])
                                                            Promising_Double_Stecker_Pairs[-1][1] += [[sorted([Crib_Deciphered_Trial[nlmm], Stecker_List_Notch[nind+1-2*(nind%2)]]), sorted([Crib_Ciphertext[nlmm], Stecker])]]
                                                        else:
                                                            Promising_Double_Stecker_Pairs[-1][1] += [[[Crib_Deciphered_Trial[nlmm], 'Unsteckered'], sorted([Crib_Ciphertext[nlmm], Stecker])]]     
                                                    
                                                    elif Crib_Ciphertext[nlmm] not in Unsteckered_Notch and Stecker not in Unsteckered_Notch and Crib_Deciphered_Trial[nlmm] not in Unsteckered_Notch and Crib_Guess[nlmm] not in Unsteckered_Notch:
                                                        if ((Crib_Ciphertext[nlmm] not in Stecker_List_Notch and Stecker not in Stecker_List_Notch) or sorted([Crib_Ciphertext[nlmm], Stecker]) in Stecker_Pairs_Notch) and ((Crib_Deciphered_Trial[nlmm] not in Stecker_List_Notch and Crib_Guess[nlmm] not in Stecker_List_Notch) or sorted([Crib_Deciphered_Trial[nlmm], Crib_Guess[nlmm]]) in Stecker_Pairs_Notch):
                                                            if Stecker != Crib_Deciphered_Trial[nlmm] and Crib_Deciphered_Trial[nlmm] != Crib_Guess[nlmm] and (list(set([Crib_Deciphered_Trial[nlmm], Crib_Guess[nlmm]]).intersection([Crib_Ciphertext[nlmm], Stecker])) == [] or sorted([Crib_Ciphertext[nlmm], Stecker]) == sorted([Crib_Deciphered_Trial[nlmm], Crib_Guess[nlmm]])):
                                                                Promising_Double_Stecker_Pairs[-1][1] += [[sorted([Crib_Deciphered_Trial[nlmm], Crib_Guess[nlmm]]), sorted([Crib_Ciphertext[nlmm], Stecker])]]    
                                                                                                                          
                                                if len(Promising_Double_Stecker_Pairs[-1][1]) == 0:
                                                    Stecker_Path_Valid = 0 # Failure to reproduce crib is nls_known region
                                                    break                                                                                                 

                                            Enigma_Tester.Switch_Plugboard(Plugboard(Stecker_Pairs_Notch))
                                            
                                            Stecker_List_Solutions = []
                                            Stecker_Pairs_Solutions = []
                                            Unsteckered_Solutions = []                                                                 
                                                                                                           
                                            Double_Stecker_Perms = list(product(*[Promising_Double_Stecker_Pair[1] for Promising_Double_Stecker_Pair in Promising_Double_Stecker_Pairs]))
                                            for Double_Stecker_Perm in Double_Stecker_Perms:
                                                Chosen_Stecker_List = []
                                                Chosen_Stecker_Pairs = []  
                                                Chosen_Unsteckered = []
                                                Solution_found = 1

                                                for Double_Stecker_Pair in Double_Stecker_Perm:
                                                    # Check for contradictions
                                                    if (Double_Stecker_Pair[0][1] == 'Unsteckered') and (Double_Stecker_Pair[0][1] in Chosen_Stecker_List):
                                                        Solution_found = 0
                                                        break
                                                    elif ((Double_Stecker_Pair[0][0] in Chosen_Stecker_List) or (Double_Stecker_Pair[0][1] in Chosen_Stecker_List)) and (sorted(Double_Stecker_Pair[0]) not in Chosen_Stecker_Pairs):
                                                        Solution_found = 0
                                                        break
                                                    elif ((Double_Stecker_Pair[1][0] in Chosen_Stecker_List) or (Double_Stecker_Pair[1][1] in Chosen_Stecker_List)) and (sorted(Double_Stecker_Pair[1]) not in Chosen_Stecker_Pairs):
                                                        Solution_found = 0
                                                        break
                                                    elif (Double_Stecker_Pair[0][0] in Chosen_Unsteckered) or (Double_Stecker_Pair[0][1] in Chosen_Unsteckered) or (Double_Stecker_Pair[1][0] in Chosen_Unsteckered) or (Double_Stecker_Pair[1][1] in Chosen_Unsteckered):
                                                        Solution_found = 0
                                                        break 

                                                    if Double_Stecker_Pair[0][1] == 'Unsteckered':
                                                        if Double_Stecker_Pair[0][0] not in Chosen_Unsteckered and Double_Stecker_Pair[0][0] not in Unsteckered_Notch:                                                    
                                                            Chosen_Unsteckered += Double_Stecker_Pair[0][0]  
                                                    elif sorted([Double_Stecker_Pair[0][0], Double_Stecker_Pair[0][1]]) not in Chosen_Stecker_Pairs and sorted([Double_Stecker_Pair[0][0], Double_Stecker_Pair[0][1]]) not in Stecker_Pairs_Notch:                                                    
                                                            Chosen_Stecker_List += [Double_Stecker_Pair[0][0], Double_Stecker_Pair[0][1]]  
                                                            Chosen_Stecker_Pairs += [sorted([Double_Stecker_Pair[0][0], Double_Stecker_Pair[0][1]])]
                                                    if sorted([Double_Stecker_Pair[1][0], Double_Stecker_Pair[1][1]]) not in Chosen_Stecker_Pairs and sorted([Double_Stecker_Pair[1][0], Double_Stecker_Pair[1][1]]) not in Stecker_Pairs_Notch:                                                        
                                                        Chosen_Stecker_List += [Double_Stecker_Pair[1][0], Double_Stecker_Pair[1][1]]  
                                                        Chosen_Stecker_Pairs += [sorted([Double_Stecker_Pair[1][0], Double_Stecker_Pair[1][1]])] 
                                                                                                                                                 
                                                if Solution_found == 1:
                                                    
                                                    Enigma_Tester.Switch_Plugboard(Plugboard(Stecker_Pairs_Notch+Chosen_Stecker_Pairs))  
                                                    Enigma_Tester.Set_Rotor_Rotations(Rotations_Test)
                                                    Enigma_Tester.Set_Ring_Settings(Ring_Settings_Test)
                                                    Message_Deciphered = Enigma_Tester.Encipher_Message_and_Restore_No_Slow(Message_Ciphertext)
                                                    Crib_Deciphered = Message_Deciphered[:len(Crib_Guess)]                                                    
                                                    if Crib_Deciphered == Crib_Guess:
                                                        Stecker_List_Solutions += [Chosen_Stecker_List]
                                                        Stecker_Pairs_Solutions += [Chosen_Stecker_Pairs]
                                                        Unsteckered_Solutions += [Chosen_Unsteckered]

                                        for nSol in range(len(Stecker_Pairs_Solutions)):
                                            
                                            Stecker_List = Stecker_List_Notch + Stecker_List_Solutions[nSol]                                        
                                            Stecker_Pairs = Stecker_Pairs_Notch + Stecker_Pairs_Solutions[nSol] 
                                            Stecker_Pairs = sorted(Stecker_Pairs, key=itemgetter(0))
                                            Unsteckered = Unsteckered_Notch + Unsteckered_Solutions[nSol] 

                                            Enigma_Tester.Switch_Plugboard(Plugboard(Stecker_Pairs))
                                            Enigma_Tester.Set_Ring_Settings(Ring_Settings_Test)                                                      
                                            Enigma_Tester.Set_Rotor_Rotations(Rotations_Test)
                                            
                                            if Countdown == "Inactive":
                                                Countdown = 1  # activate timer to exit after this nr2 step                                                                                                                         
                                                
                                            nlp_soln += [nlp]
                                            Message_Enciphered = Enigma_Tester.Encipher_Message_and_Restore(Message_Plaintext)                                                    
                                            Message_Deciphered = Enigma_Tester.Encipher_Message_and_Restore(Message_Ciphertext)
                                            
                                            Crib_Solutions += [[Rotor_Models, [Enigma_Tester.Rotors[0].Rotation, Enigma_Tester.Rotors[1].Rotation, Enigma_Tester.Rotors[2].Rotation], [Enigma_Tester.Rotors[0].Ring_Setting, Enigma_Tester.Rotors[1].Ring_Setting, Enigma_Tester.Rotors[2].Ring_Setting], Stecker_Pairs, Message_Deciphered[:len(Crib_Guess)], Message_Deciphered[len(Crib_Guess):]]]                                 
                                                  
                                            # A quasi-cheating section to simulate human completion / prediction of partial words [for len(Stecker_Pairs) == Total_Steckers - 1 this is entirely reasonable]
                                            while len(Stecker_Pairs) < Nstc:
                                                                                                        
                                                Steckers_remaining = Nstc - len(Stecker_Pairs)
                                                Count_NmX_Steckers[Steckers_remaining] += 1
                                                Nstc_current = len(Stecker_Pairs)
    
                                                for na in range((len(Message_Deciphered)-26)/26):  # subtracts the first 26 Letters (Crib plus remainder of first fast rotor cycle)
                                                    nlk_Steckered = [nlk for nlk in range(26*na, 26*na+len(Crib_Guess)) if ((Message_Ciphertext[nlk] in Stecker_List or Message_Ciphertext[nlk] in Unsteckered) and (Message_Deciphered[nlk] in Stecker_List or Message_Deciphered[nlk] in Unsteckered))]                                                                                 
                                                                                                                                                                                                                      
                                                    In_Phase = 1
                                                    for nlks in nlk_Steckered:
                                                        if Message_Deciphered[nlks] != Message_Plaintext[nlks]:
                                                            In_Phase = 0
                                                            break
                                                    if In_Phase == 0:
                                                        continue
                                                    else: 
                                                        nlk_Partial = [nlk for nlk in range(26*na, 26*na+len(Crib_Guess)) if ((Message_Ciphertext[nlk] in Stecker_List or Message_Ciphertext[nlk] in Unsteckered) or (Message_Plaintext[nlk] in Stecker_List or Message_Plaintext[nlk] in Unsteckered)) and (Message_Deciphered[nlk] != Message_Plaintext[nlk])]                                                    
                                                        for nlkp in nlk_Partial:  
                                                            # What about only for if Message_Deciphered[nlkp+/-1] = Message_Plaintext[nlkp+/-1] ?
                                                            if (Message_Plaintext[nlkp] not in Stecker_List) and (Message_Plaintext[nlkp] not in Unsteckered): 
                                                                
                                                                Stecker_List += sorted([Message_Deciphered[nlkp], Message_Plaintext[nlkp]])
                                                                Stecker_Pairs += [sorted([Message_Deciphered[nlkp], Message_Plaintext[nlkp]])]
                                                                Stecker_Pairs = sorted(Stecker_Pairs, key=itemgetter(0))    
                                                                Enigma_Tester.Switch_Plugboard(Plugboard(Stecker_Pairs))
                                                                Message_Enciphered = Enigma_Tester.Encipher_Message_and_Restore(Message_Plaintext)                                                                 
                                                                Message_Deciphered = Enigma_Tester.Encipher_Message_and_Restore(Message_Ciphertext)                                                                 
                                                                break  # need to update nlk_Steckered, nlk_Partial       
                                                                                                           
                                                            elif (Message_Ciphertext[nlkp] not in Stecker_List) and (Message_Ciphertext[nlkp] not in Unsteckered):                                                                
                                                                                                                             
                                                                Stecker_List += sorted([Message_Enciphered[nlkp], Message_Ciphertext[nlkp]])
                                                                Stecker_Pairs += [sorted([Message_Enciphered[nlkp], Message_Ciphertext[nlkp]])]
                                                                Stecker_Pairs = sorted(Stecker_Pairs, key=itemgetter(0))    
                                                                Enigma_Tester.Switch_Plugboard(Plugboard(Stecker_Pairs))
                                                                Message_Enciphered = Enigma_Tester.Encipher_Message_and_Restore(Message_Plaintext)                                                                 
                                                                Message_Deciphered = Enigma_Tester.Encipher_Message_and_Restore(Message_Ciphertext)                                                                  
                                                                break  # need to update nlk_Steckered, nlk_Partial   

                                                        if len(Stecker_Pairs) > Nstc - Steckers_remaining:
                                                            Steckers_remaining = Nstc - len(Stecker_Pairs)
                                                            break  # need to update nlk_Steckered, nlk_Partial      
                                                if len(Stecker_Pairs) == Nstc_current:
                                                    #print "Not all steckers found!"                
                                                    break    
                                
                                            if len(Stecker_Pairs) == Nstc:   
                                                               
                                                Count_NmX_Steckers[0] += 1   
                                                Enigma_Tester.Set_Ring_Settings(Ring_Settings_Test)
                                                Enigma_Tester.Set_Rotor_Rotations(Rotations_Test)
                                                Message_Deciphered = Enigma_Tester.Encipher_Message_and_Restore(Message_Ciphertext)  
                                                        
                                                nl_mid = Enigma_Tester.Number_of_Steps("Middle Rotor Advance") - 1
                                                nl_exp = Enigma_Tester.Number_of_Steps("Slow Rotor Advance") - 1  # -1 because the mechanical step will then occur before electronic step in this position [eg if one advance = change then nl_exp is position 0 (since key press advances before electronic step)
                                                nl_act = str(len(Message_Deciphered)+1)+'+'
                                                                                                  
                                                                                                                            
                                                for nl in range(len(Message_Deciphered)):     
                                                    if (Message_Deciphered[nl] != Message_Plaintext[nl]):
                                                        nl_act = nl
                                                        # Solves problem when subsequent 'out-of-phase' letter(s) matches by chance        
                                                        nl_act -= (nl_act - (nl_mid+1))%26 
                                                        break                  
            
                                                Output_Corrected  = 1                                            
                                                New_Middle_Rotation_0 = "None"
                                                New_Middle_Ring_Setting_0 = "None"                                                                                                                                                                                                    
                                                if nl_exp >= len(Message_Deciphered):  # If current initial Rotations would lead to slow rotor advancing after message
                                                    if type(nl_act) is str:             # If deciphered message is correct throughout
                                                        #print "nl_exp, nl_act both after"
                                                        nmlt = 0
                                                        while nl_exp - nmlt*26 >= len(Message_Plaintext):  #len(Message_Plaintext)-3:
                                                            nmlt0 = nmlt
                                                            nmlt += 1
                                                        nmlt = 0    
                                                        while nl_exp + nmlt*26 <= 650: #(650 = 26*25; 25 not 26 due to double-step mechanism)
                                                            nmlt1 = nmlt
                                                            nmlt += 1   
                                                        New_Middle_Rotation_0 = Advance_Letter(Enigma_Start.Rotors[1].Rotation, (nmlt0-1))
                                                        New_Middle_Ring_Setting_0 = Advance_Letter(Enigma_Start.Rotors[1].Ring_Setting, (nmlt0-1))                     
                                                        New_Middle_Rotation_1 = Advance_Letter(Enigma_Start.Rotors[1].Rotation, -(nmlt1-1))
                                                        New_Middle_Ring_Setting_1 = Advance_Letter(Enigma_Start.Rotors[1].Ring_Setting, -(nmlt1-1))                        

                                                    else:    # If deciphered message turns to gibberish at some point (indicating slow rotor advance)      
                                                        #print "nl_exp after, nl_act =", nl_act
                                                        nmlt1 = (nl_act - (nl_mid+1)) / 26                                                                                          
                                                        #  -(nmlt1+1) due to middle rotor advancing at both nl_adv-1 and nl_adv                                                  
                                                        New_Middle_Rotation_1 = Advance_Letter(Enigma_Start.Rotors[1].Notches[0], -(nmlt1+1))
                                                        New_Middle_Ring_Setting_1 = Advance_Letter(Ring_Settings_Test[1], (ord(New_Middle_Rotation_1)-ord(Rotations_Test[1]))%26)                                                                                                                                                                                                                 
  
                                                elif nl_act == nl_exp: 
                                                    nl_rtn = str(len(Message_Deciphered)+1)+'+'                                     
                                                    na = 0
                                                    while nl_act + na*26 < min(650,len(Message_Deciphered)):
                                                        In_Phase = 1
                                                        for nl in range(nl_act+na*26, min(nl_act+(na+1)*26,min(650,len(Message_Deciphered)))):
                                                            if (Message_Deciphered[nl] != Message_Plaintext[nl]) and nl in [nl1+nl_act+na*26 for nl1 in nls_known[nnEO]]:
                                                                In_Phase = 0
                                                                break
                                                        if In_Phase == 1:
                                                            nl_rtn = nl_act+na*26
                                                            break           
                                                        na += 1
                                                                                                                                                                        
                                                    if type(nl_rtn) is str: 
                                                        #print "nl_act = nl_exp, nl_rtn after"                                                                                                               
                                                        nl_rtn = nl_exp
                                                        nmlt0 = 0      
                                                        while nl_rtn < len(Message_Deciphered):
                                                            nmlt0 += 1 
                                                            nl_rtn = nl_exp + 26*nmlt0
                                                        nmlt1 = nmlt0       
                                                        while nl_rtn <= 650: #(650 = 26*25; 25 not 26 due to double-step mechanism)
                                                            nmlt1 += 1  
                                                            nl_rtn = nl_exp + 26*nmlt1  
            
                                                        New_Middle_Rotation_0 = Advance_Letter(Rotations_Test[1], -nmlt0)
                                                        New_Middle_Ring_Setting_0 = Advance_Letter(Ring_Settings_Test[1], -nmlt0) 
                                                        New_Middle_Rotation_1 = Advance_Letter(Rotations_Test[1], -(nmlt1-1))
                                                        New_Middle_Ring_Setting_1 = Advance_Letter(Ring_Settings_Test[1], -(nmlt1-1))                                                                                                                                                                                                                                                                                                
                                                    else: 
                                                        #print "nl_act = nl_exp, nl_rtn =", nl_rtn
                                                        nmlt1 = (nl_rtn - nl_exp) / 26
                                                        New_Middle_Rotation_1 = Advance_Letter(Rotations_Test[1], -nmlt1)
                                                        New_Middle_Ring_Setting_1 = Advance_Letter(Ring_Settings_Test[1], -nmlt1) 
                                            
                                                elif Message_Deciphered == Message_Plaintext:
                                                    New_Middle_Rotation_1 = Rotations_Test[1]
                                                    New_Middle_Ring_Setting_1 = Ring_Settings_Test[1]      
                                                    
                                                # Have a problem where nl_act is never found (too early in message?) 
                                                else:  
                                                    #print "Else option"  
                                                    Enigma_Tester.Set_Ring_Settings(Ring_Settings_Test)
                                                    Enigma_Tester.Set_Rotor_Rotations(Rotations_Test) 
                                                    nmlt1 = (nl_exp-nl_act) / 26
                                                    New_Middle_Rotation_1 = Advance_Letter(Rotations_Test[1], nmlt1)
                                                    New_Middle_Ring_Setting_1 = Advance_Letter(Ring_Settings_Test[1], nmlt1) 
                                                            
                                                if Output_Corrected == 1: 
                                                    Enigma_Tester.Set_Rotor_Rotations([Rotations_Test[0], New_Middle_Rotation_1, Rotations_Test[2]])
                                                    Enigma_Tester.Set_Ring_Settings([Ring_Settings_Test[0], New_Middle_Ring_Setting_1, Ring_Settings_Test[2]])                                
                                                    Message_Deciphered = Enigma_Tester.Encipher_Message_and_Restore(Message_Ciphertext)  

                                                    if Message_Deciphered == Message_Plaintext:
                                                        if New_Middle_Rotation_0 == "None" or New_Middle_Rotation_0 == New_Middle_Rotation_1:
                                                            if [Rotor_Models, [[Enigma_Tester.Rotors[0].Rotation, New_Middle_Rotation_1, Enigma_Tester.Rotors[2].Rotation], "None"], [[Ring_Settings_Test[0], New_Middle_Ring_Setting_1, Ring_Settings_Test[2]], "None"], Stecker_Pairs, Message_Deciphered[:len(Crib_Guess)], Message_Deciphered[len(Crib_Guess):]] not in Full_Solutions:
                                                                Full_Solutions += [[Rotor_Models, [[Enigma_Tester.Rotors[0].Rotation, New_Middle_Rotation_1, Enigma_Tester.Rotors[2].Rotation], "None"], [[Ring_Settings_Test[0], New_Middle_Ring_Setting_1, Ring_Settings_Test[2]], "None"], Stecker_Pairs, Message_Deciphered[:len(Crib_Guess)], Message_Deciphered[len(Crib_Guess):]]]                                                       
                                                        else:
                                                            if [Rotor_Models, [[Enigma_Tester.Rotors[0].Rotation, New_Middle_Rotation_1, Enigma_Tester.Rotors[2].Rotation], [Enigma_Tester.Rotors[0].Rotation, New_Middle_Rotation_0, Enigma_Tester.Rotors[2].Rotation]], [[Ring_Settings_Test[0], New_Middle_Ring_Setting_1, Ring_Settings_Test[2]], [Ring_Settings_Test[0], New_Middle_Ring_Setting_0, Ring_Settings_Test[2]]], Stecker_Pairs, Message_Deciphered[:len(Crib_Guess)], Message_Deciphered[len(Crib_Guess):]] not in Full_Solutions:
                                                                Full_Solutions += [[Rotor_Models, [[Enigma_Tester.Rotors[0].Rotation, New_Middle_Rotation_1, Enigma_Tester.Rotors[2].Rotation], [Enigma_Tester.Rotors[0].Rotation, New_Middle_Rotation_0, Enigma_Tester.Rotors[2].Rotation]], [[Ring_Settings_Test[0], New_Middle_Ring_Setting_1, Ring_Settings_Test[2]], [Ring_Settings_Test[0], New_Middle_Ring_Setting_0, Ring_Settings_Test[2]]], Stecker_Pairs, Message_Deciphered[:len(Crib_Guess)], Message_Deciphered[len(Crib_Guess):]]]                                                           
                                            else:
                                                print "Not all steckers found!"    

                            # if contradiction was found [Stecker_Path_Valid = 0] -> can check for other implied contradictions                                                        
                            elif (Implied_Contradictions == 1) and (nnE_Cont[nE] > nnEO): 
                                nnE_adv = nnE_Cont[nE] - nnEO + 1                    
                            
                            if (Exit_If_Found == 1) and (Countdown == 0):    
                                # really want this at the end after exiting the "Crack_Engima function"
                                print '...', Stalls
                                Counts = [Count_Rotations, Count_Scrambler_Letters, Count_Scrambler_Notches, Count_Valid_Paths, Count_Valid_Cribs, Count_NmX_Steckers, len(Erroneous_Crib_Solutions), len(Partial_Crib_Solutions), len(Crib_Solutions), len(Full_Solutions)]
                                                                         
                                return [Full_Solutions, Crib_Solutions, Partial_Crib_Solutions, Erroneous_Crib_Solutions, Counts]                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                
                            # Advance current middle rotor in enigma sequence
                            if nnEO < NE:
                                nEO = nE_RevOrder[nnEO] 
                                for na in range(nnE_adv):
                                    Enigma_Chain[nEO].Rotors[1].Rotation = Advance_Letter(Enigma_Chain[nEO].Rotors[1].Rotation)      
                                    nnEO += 1
                                    nEO = nE_RevOrder[min(nnEO,NE-1)]
                                nnE_adv = 1  # reset jump
                            else:
                                nnEO += 1                            

                        # Retreat all middle rotors in enigma sequence
                        for nEO in nE_RevOrder:
                            Enigma_Chain[nEO].Rotors[1].Rotation = Advance_Letter(Enigma_Chain[nEO].Rotors[1].Rotation, -1)

                    for nE in range(NE):
                        Enigma_Chain[nE].Rotors[0].Rotation = Advance_Letter(Enigma_Chain[nE].Rotors[0].Rotation)                
                    Enigma_Start.Rotors[0].Rotation = Advance_Letter(Enigma_Start.Rotors[0].Rotation)
                for nE in range(NE):
                    Enigma_Chain[nE].Rotors[1].Rotation = Advance_Letter(Enigma_Chain[nE].Rotors[1].Rotation)                       
                Enigma_Start.Rotors[1].Rotation = Advance_Letter(Enigma_Start.Rotors[1].Rotation)        
            for nE in range(NE):
                Enigma_Chain[nE].Rotors[2].Rotation = Advance_Letter(Enigma_Chain[nE].Rotors[2].Rotation)
            Enigma_Start.Rotors[2].Rotation = Advance_Letter(Enigma_Start.Rotors[2].Rotation)   
            
        print '...', Stalls,                                                                                
    print ''
    
    Counts = [Count_Rotations, Count_Scrambler_Letters, Count_Scrambler_Notches, Count_Valid_Paths, Count_Valid_Cribs, Count_NmX_Steckers, len(Erroneous_Crib_Solutions), len(Partial_Crib_Solutions), len(Crib_Solutions), len(Full_Solutions)]
    return [Full_Solutions, Crib_Solutions, Partial_Crib_Solutions, Erroneous_Crib_Solutions, Counts]

# Function to return all possible day keys based on calculated enigma settings and enciphered message key
def Calculate_Possible_Day_Keys(Full_Solutions, Message_Key_Enciphered):
    
    # Just uses the first (probably the only) solution:
    
    Rotor_Models_Calc = Full_Solutions[0][0] 
    Message_Key_Calc_0 = Full_Solutions[0][1][0]   
    Message_Key_Calc_1 = Full_Solutions[0][1][1]    
    Ring_Settings_Calc_0 = Full_Solutions[0][2][0]
    Ring_Settings_Calc_1 = Full_Solutions[0][2][1]
  
    #print Message_Key_Calc_0, Message_Key_Calc_1, Ring_Settings_Calc_0, Ring_Settings_Calc_1     

    if Message_Key_Calc_1 == "None":
        Message_Keys_Calc = [Message_Key_Calc_0]
        Ring_Settings_Calc = [Ring_Settings_Calc_0] 
    else:
        if (ord(Ring_Settings_Calc_1[1])-ord(Ring_Settings_Calc_0[1]))%26 == (ord(Message_Key_Calc_1[1])-ord(Message_Key_Calc_0[1]))%26:
            print "Big problems! Message_Key offset not equal to Ring_Settings offset!"
        Message_Keys_Calc = []
        Ring_Settings_Calc = []  
        for nmk in range((ord(Message_Key_Calc_1[1])-ord(Message_Key_Calc_0[1]))%26+1):
            Message_Keys_Calc += [[Message_Key_Calc_0[0], Advance_Letter(Message_Key_Calc_0[1], nmk), Message_Key_Calc_0[2]]]
            Ring_Settings_Calc += [[Ring_Settings_Calc_0[0], Advance_Letter(Ring_Settings_Calc_0[1], nmk), Ring_Settings_Calc_0[2]]]  

    Stecker_Pairs_Calc = Full_Solutions[0][3]
    PB = Plugboard(Stecker_Pairs_Calc)          
                       
    #Day_Key_Base = ['A', 'A', 'A']                    
                          
    Rotors = []
    for nR in range(len(Rotor_Models_Calc)):
        #Rotors += [Rotor(Rotor_Models_Calc[nR], Day_Key_Base[nR], Ring_Settings_Calc_0[nR])]  
        Rotors += [Rotor(Rotor_Models_Calc[nR], 'A', Ring_Settings_Calc_0[nR])]  

    #Rotors[1].Rotation = Rotors[1].Notches[0]
    
    Rfl = Reflector('B')
    Enigma_AN3 = Enigma(PB, Rotors, Rfl)
           
    Day_Key_Solutions = []
    for nshift_Slow in range(0,26):
        for nmk in range(len(Message_Keys_Calc)):
            Message_Key_Input = [Message_Keys_Calc[nmk][0], Message_Keys_Calc[nmk][1], Advance_Letter(Message_Keys_Calc[nmk][2], nshift_Slow)]
            Ring_Settings_Input = [Ring_Settings_Calc[nmk][0], Ring_Settings_Calc[nmk][1], Advance_Letter(Ring_Settings_Calc[nmk][2], nshift_Slow)]
            Enigma_AN3.Set_Ring_Settings(Ring_Settings_Input)
            for nr2 in range(0,26):
                for nr1 in range(0,26):
                    for nr0 in range(0,26):
                        Enigma_AN3.Set_Rotor_Rotations([chr(nr0+65), chr(nr1+65), chr(nr2+65)]) 
                        Message_Key_Enciphered_Trial = Enigma_AN3.Encipher_Message(Message_Key_Input[0]+Message_Key_Input[1]+Message_Key_Input[2])   
                        if Message_Key_Enciphered_Trial == Message_Key_Enciphered[0]+Message_Key_Enciphered[1]+Message_Key_Enciphered[2]:
                            Day_Key_Solutions += [[chr(nr0+65), chr(nr1+65), chr(nr2+65)]]                
    Day_Key_Solutions = sorted(Day_Key_Solutions, key=itemgetter(0,1,2))
                    
    return Day_Key_Solutions

# Perform trials to recover day key from a second encoded message with this key (no known crib)
def Perform_Day_Key_Trials(Full_Solutions, Day_Key_Input, Prose_Trial_Plaintext):
                      
    Prose_Trial_Plaintext = (Prose_Trial_Plaintext.translate(None, string.punctuation)).upper().replace(" ", "")       
    
    Rotor_Models_Calc = Full_Solutions[0][0] 
    Message_Key_Calc_0 = Full_Solutions[0][1][0]   
    Message_Key_Calc_1 = Full_Solutions[0][1][1]    
    Ring_Settings_Calc_0 = Full_Solutions[0][2][0]
    Ring_Settings_Calc_1 = Full_Solutions[0][2][1]    
    
    if Message_Key_Calc_1 == "None":
        Message_Keys_Calc = [Message_Key_Calc_0]
        Ring_Settings_Calc = [Ring_Settings_Calc_0] 
    else:
        # NEEDS DOING!
        Message_Keys_Calc = [Message_Key_Calc_0]
        Ring_Settings_Calc = [Ring_Settings_Calc_0]  

    Stecker_Pairs_Calc = Full_Solutions[0][3]
    PB = Plugboard(Stecker_Pairs_Calc)          
                        
    Rotors = []
    for nR in range(len(Rotor_Models_Calc)):
        Rotors += [Rotor(Rotor_Models_Calc[nR], Day_Key_Input[nR], Ring_Settings_Calc_0[nR])]  
    Rfl = Reflector('B')
    Enigma_AN3 = Enigma(PB, Rotors, Rfl) 
    
    Message_Key_Trial = [chr(randint(65,90)), chr(randint(65,90)), chr(randint(65,90))]
    Message_Key_Trial_Enciphered = Enigma_AN3.Encipher_Message(Message_Key_Trial[0]+Message_Key_Trial[1]+Message_Key_Trial[2])
    Enigma_AN3.Set_Rotor_Rotations(Message_Key_Trial)
    Prose_Trial_Ciphertext = Enigma_AN3.Encipher_Message(Prose_Trial_Plaintext)
    Message_Trial_Ciphertext = Message_Key_Trial_Enciphered + Prose_Trial_Ciphertext
        
    Day_Key_Trials = []
    for Day_Key_Solution in Day_Key_Solutions:
         Enigma_AN3.Set_Rotor_Rotations(Day_Key_Solution)
         Message_Key_Trial_Deciphered = Enigma_AN3.Encipher_Message(Message_Trial_Ciphertext[:3])
         Enigma_AN3.Set_Rotor_Rotations(Message_Key_Trial_Deciphered) 
         Prose_Trial_Deciphered = Enigma_AN3.Encipher_Message(Message_Trial_Ciphertext[3:])
         Day_Key_Trials += [[Day_Key_Solution, infer_spaces(Prose_Trial_Deciphered.lower())]]
                         
    return Day_Key_Trials                    
                                                            
# ****************************************************************** #

# Main

start = time.time()

print "\nENIGMA & quasi-BOMBE simulation.  David Hoffmann 2017."

# *********************  Crib & Prose  *********************** #

Crib_Plaintext = "Wettervorhersagebiskaya"
Crib_Plaintext = (Crib_Plaintext.translate(None, string.punctuation)).upper()
Crib_Plaintext = Crib_Plaintext.replace(" ", "")

Prose_Plaintext = []
# 0
Prose_Plaintext += ["We believe that we can change the things around us in accordance with our desires - we believe it because otherwise we can see no favourable outcome. We do not think of the outcome which generally comes to pass and is also favourable: we do not succeed in changing things in accordance with our desires, but gradually our desires change. The situation that we hoped to change because it was intolerable becomes unimportant to us. We have failed to surmount the obstacle, as we were absolutely determined to do, but life has taken us round it, led us beyond it, and then if we turn round to gaze into the distance of the past, we can barely see it, so imperceptible has it become."]
# 1
Prose_Plaintext += ["Sometimes fate is like a small sandstorm that keeps changing directions. You change direction but the sandstorm chases you. You turn again, but the storm adjusts. Over and over you play this out, like some ominous dance with death just before dawn. Why? Because this storm isn\'t something that blew in from far away, something that has nothing to do with you. This storm is you. Something inside of you. So all you can do is give in to it, step right inside the storm, closing your eyes and plugging up your ears so the sand doesn\'t get in, and walk through it, step by step. There\'s no sun there, no moon, no direction, no sense of time. Just fine white sand swirling up into the sky like pulverized bones. That\'s the kind of sandstorm you need to imagine."]
# 2
Prose_Plaintext += ["The most important things are the hardest to say. They are the things you get ashamed of, because words diminish them - words shrink things that seemed limitless when they were in your head to no more than living size when they\'re brought out. But it\'s more than that, isn\'t it? The most important things lie too close to wherever your secret heart is buried, like landmarks to a treasure your enemies would love to steal away. And you may make revelations that cost you dearly only to have people look at you in a funny way, not understanding what you\'ve said at all, or why you thought it was so important that you almost cried while you were saying it. That\'s the worst, I think. When the secret stays locked within not for want of a teller but for want of an understanding ear."]
# 3
Prose_Plaintext += ["If you\'re going to try, go all the way. Otherwise, don\'t even start. This could mean losing girlfriends, wives, relatives and maybe even your mind. It could mean not eating for three or four days. It could mean freezing on a park bench. It could mean jail. It could mean derision. It could mean mockery-isolation. Isolation is the gift. All the others are a test of your endurance, of how much you really want to do it. And, you\'ll do it, despite rejection and the worst odds. And it will be better than anything else you can imagine. If you\'re going to try, go all the way. There is no other feeling like that. You will be alone with the gods, and the nights will flame with fire. You will ride life straight to perfect laughter. It\'s the only good fight there is."]
# 4
Prose_Plaintext += ["A green hunting cap squeezed the top of the fleshy balloon of a head. The green earflaps, full of large ears and uncut hair and the fine bristles that grew in the ears themselves, stuck out on either side like turn signals indicating two directions at once. Full, pursed lips protruded beneath the bushy black moustache and, at their corners, sank into little folds filled with disapproval and potato chip crumbs. In the shadow under the green visor of the cap Ignatius J. Reilly\'s supercilious blue and yellow eyes looked down upon the other people waiting under the clock at the D.H. Holmes department store, studying the crowd of people for signs of bad taste in dress. Several of the outfits, Ignatius noticed, were new enough and expensive enough to be properly considered offenses against taste and decency. Possession of anything new or expensive only reflected a person\'s lack of theology and geometry; it could even cast doubts upon one\'s soul."]  # A Confederacy Of Dunces (John Kennedy Toole)
# 5
Prose_Plaintext += ["Call me Ishmael. Some years ago - never mind how long precisely - having little or no money in my purse, and nothing particular to interest me on shore, I thought I would sail about a little and see the watery part of the world. It is a way I have of driving off the spleen, and regulating the circulation. Whenever I find myself growing grim about the mouth; whenever it is a damp, drizzly November in my soul; whenever I find myself involuntarily pausing before coffin warehouses, and bringing up the rear of every funeral I meet; and especially whenever my hypos get such an upper hand of me, that it requires a strong moral principle to prevent me from deliberately stepping into the street, and methodically knocking people\'s hats off - then, I account it high time to get to sea as soon as I can. This is my substitute for pistol and ball. With a philosophical flourish Cato throws himself upon his sword; I quietly take to the ship. There is nothing surprising in this. If they but knew it, almost all men in their degree, some time or other, cherish very nearly the same feelings towards the ocean with me."]  # Moby Dick (Herman Melville)
# 6
Prose_Plaintext += ["In the late summer of that year we lived in a house in a village that looked across the river and the plain to the mountains. In the bed of the river there were pebbles and boulders, dry and white in the sun, and the water was clear and swiftly moving and blue in the channels. Troops went by the house and down the road and the dust they raised powdered the leaves of the trees. The trunks of the trees too were dusty and the leaves fell early that year and we saw the troops marching along the road and the dust rising and leaves, stirred by the breeze, falling and the soldiers marching and afterward the road bare and white except for the leaves."]  # A Farewell To Arms (Ernest Hemingway)
# 7
Prose_Plaintext += ["It was the best of times, it was the worst of times, it was the age of wisdom, it was the age of foolishness, it was the epoch of belief, it was the epoch of incredulity, it was the season of Light, it was the season of Darkness, it was the spring of hope, it was the winter of despair, we had everything before us, we had nothing before us, we were all going direct to Heaven, we were all going direct the other way - in short, the period was so far like the present period, that some of its noisiest authorities insisted on its being received, for good or for evil, in the superlative degree of comparison only."]  # A Tale Of Two Cities (Charles Dickens)
# 8
Prose_Plaintext += ["I first met Dean not long after my wife and I split up. I had just gotten over a serious illness that I won\'t bother to talk about, except that it had something to do with the miserably weary split-up and my feeling that everything was dead. With the coming of Dean Moriarty began the part of my life you could call my life on the road. Before that I\'d often dreamed of going West to see the country, always vaguely planning and never taking off. Dean is the perfect guy for the road because he actually was born on the road, when his parents were passing through Salt Lake City in 1926, in a jalopy, on their way to Los Angeles. First reports of him came to me through Chad King, who\'d shown me a few Letters from him written in a New Mexico reform school. I was tremendously interested in the Letters because they so naively and sweetly asked Chad to teach him all about Nietzsche and all the wonderful intellectual things that Chad knew. At one point Carlo and I talked about the Letters and wondered if we would ever meet the strange Dean Moriarty. This is all far back, when Dean was not the way he is today, when he was a young jailkid shrouded in mystery. Then news came that Dean was out of reform school and was coming to New York for the first time; also there was talk that he had just married a girl called Marylou."]  # On The Road (Jack Kerouac)
# 9
Prose_Plaintext += ["Hale knew, before he had been in Brighton three hours, that they meant to murder him. With his inky fingers and his bitten nails, his manner cynical and nervous, anybody could tell he didn\'t belong - belong to the early summer sun, the cool Whitsun wind off the sea, the holiday crowd. They came in by train from Victoria every five minutes, rocked down Queen\'s Road standing on the tops of the little local trams, stepped off in bewildered multitudes into fresh and glittering air: the new silver paint sparkled on the piers, the cream houses ran away into the west like a pale Victorian water-colour; a race in miniature motors, a band playing, flower gardens in bloom below the front, an aeroplane advertising something for the health in pale vanishing clouds across the sky."]  # Brighton Rock (Graham Greene)
# 10
Prose_Plaintext += ["It must have been around a quarter to eleven. A sailor came in and ordered a chile dog and coffee. I sliced a bun, jerked a frank out of the boiling water, nested it, poured a half-dipper of chile over the frank and sprinkled it liberally with chopped onions. I scribbled a check and put it by his plate. I wouldn\'t have recommended the unpalatable mess to a starving animal. The sailor was the only customer, and after he ate his dog he left. That was the exact moment she entered. A small woman, hardly more than five feet. She had the figure of a teenage girl. Her suit was a blue tweed, smartly cut, and over her thin shoulders she wore a fur jacket, bolero length. Tiny gold circular earrings clung to her small pierced ears. Her hands and feet were small, and when she seated herself at the counter I noticed she wasn\'t wearing any rings."]  # Pick-Up (Charles Willeford)
# 11
Prose_Plaintext += ["Dark spruce forest frowned on either side of the frozen waterway. The trees had been stripped by a recent wind of their white covering of frost, and they seemed to lean toward each other, black and ominous, in the fading light. A vast silence reigned over the land. The land itself was a desolation, lifeless, without movement, so lone and cold that the spirit of it was not even that of sadness. There was a hint in it of laughter, but of a laughter more terrible than any sadness - a laughter that was mirthless as the smile of the Sphinx, a laughter cold as the frost and partaking of the grimness of infallibility. It was the masterful and incommunicable wisdom of eternity laughing at the futility of life and the effort of life. It was the Wild, the savage, frozen-hearted Northland Wild."]  # White Fang (Jack London)
# 12
Prose_Plaintext += ["I am a sick man. ... I am a spiteful man. I am an unattractive man. I believe my liver is diseased. However, I know nothing at all about my disease, and do not know for certain what ails me. I don't consult a doctor for it, and never have, though I have a respect for medicine and doctors. Besides, I am extremely superstitious, sufficiently so to respect medicine, anyway (I am well-educated enough not to be superstitious, but I am superstitious). No, I refuse to consult a doctor from spite. That you probably will not understand. Well, I understand it, though. Of course, I can't explain who it is precisely that I am mortifying in this case by my spite: I am perfectly well aware that I cannot pay out the doctors by not consulting them; I know better than anyone that by all this I am only injuring myself and no one else. But still, if I don't consult a doctor it is from spite. My liver is bad, well then let it hurt even worse!"]  # Notes From Underground (Fyodor Dostoevsky)
# 13
Prose_Plaintext += ["No live organism can continue for long to exist sanely under conditions of absolute reality; even larks and katydids are supposed, by some, to dream. Hill House, not sane, stood by itself against its hills, holding darkness within; it had stood so for eighty years and might stand for eighty more. Within, walls continued upright, bricks met neatly, floors were firm, and doors were sensibly shut; silence lay steadily against the wood and stone of Hill House, and whatever walked there, walked alone..."]  # The Haunting Of Hill House (Shirley Jackson)
# 14
Prose_Plaintext += ["I am an invisible man. No, I am not a spook like those who haunted Edgar Allan Poe; nor am I one of your Hollywood-movie ectoplasms. I am a man of substance, of flesh and bone, fiber and liquids-and I might even be said to possess a mind. I am invisible, understand, simply because people refuse to see me. Like the bodiless heads you see sometimes in circus sideshows, it is as though I have been surrounded by mirrors of hard, distorting glass. When they approach me they see only my surroundings, themselves, or figments of their imagination-indeed, everything and anything except me."]  # Invisible Man (Ralph Ellison)
# 15
Prose_Plaintext += ["You don't know about me without you have read a book by the name of The Adventures of Tom Sawyer; but that ain't no matter. That book was made by Mr. Mark Twain, and he told the truth, mainly. There was things which he stretched, but mainly he told the truth. That is nothing. I never seen anybody but lied one time or another, without it was Aunt Polly, or the widow, or maybe Mary. Aunt Polly - Tom's Aunt Polly, she is - and Mary, and the Widow Douglas is all told about in that book, which is mostly a true book, with some stretchers, as I said before."]  # The Adventures Of Huckleberry Finn (Mark Twain)
# 16
#Prose_Plaintext += ["Now this is not the end. It is not even the beginning of the end. But it is, perhaps, the end of the beginning."]

nProse = randint(0,len(Prose_Plaintext)-1)

# *********************  Initial Encryption  *********************** #

Alphabet = list('ABCDEFGHIJKLMNOPQRSTUVWXYZ')

Rotors_Yesterday = ['I', 'II', 'III']

# Enigma initial configuration
#Rotor_Models_Input = ['II', 'III', 'I']       # Rotor types
Rotor_Perms = [Rotor_Perm for Rotor_Perm in list(permutations(['I','II','III'],3)) if (Rotor_Perm[0]!=Rotors_Yesterday[0] and Rotor_Perm[1]!=Rotors_Yesterday[1] and Rotor_Perm[2]!=Rotors_Yesterday[2])]
Rotor_Models_Input = random.choice(Rotor_Perms)

Day_Key_Input = [chr(randint(65,90)), chr(randint(65,90)), chr(randint(65,90))]   # [Day Key] Initial rotor Rotation settings
Ring_Settings_Input = [chr(randint(65,90)), chr(randint(65,90)), chr(randint(65,90))]    # Ring settings (internal wiring vs Alphabet ring & Notches)
Message_Key_Input = [chr(randint(65,90)), chr(randint(65,90)), chr(randint(65,90))]   # Initial rotor Rotation settings
#Message_Key_Input = [chr(randint(65,90)), chr(randint(65,90)), chr((ord(Ring_Settings_Input[2])-65+randint(0,3))%26+65)]   # Initial rotor Rotation settings

Stecker_Pairs_Input = []
Alphabet_ongoing = deepcopy(Alphabet)
if Total_Steckers == 0:
    Nstc = randint(0,10)
else: 
    Nstc = Total_Steckers
for nstc in range(Nstc):
    Letter0 = Alphabet_ongoing[randint(0,len(Alphabet_ongoing)-1)]
    Alphabet_ongoing.remove(Letter0)
    if Adjacent_Steckers == 0:
        Alphabet_second = [Letter for Letter in Alphabet_ongoing if ((chr(ord(Letter)+1) != Letter0) and (chr(ord(Letter)-1) != Letter0))]
    else:
        Alphabet_second = Alphabet_ongoing
    Letter1 = Alphabet_second[randint(0,len(Alphabet_second)-1)]
    Alphabet_ongoing.remove(Letter1)
    Stecker_Pairs_Input += [sorted([Letter0, Letter1])]
Stecker_Pairs_Input = sorted(Stecker_Pairs_Input, key=itemgetter(0))
PB = Plugboard(Stecker_Pairs_Input) 

# Manual Inputs

#nProse = 0
#Rotor_Models_Input = ['III', 'II', 'I']   # Rotor types
#Day_Key_Input = ['G', 'P', 'W']           # [Day Key] Initial rotor Rotation settings
#Ring_Settings_Input = ['I', 'T', 'U']     # Ring settings (internal wiring vs Alphabet ring & Notches)
#Message_Key_Input = ['W', 'D', 'V']       # Initial rotor Rotation settings
#Stecker_Pairs_Input = [['A', 'G'], ['B', 'Q'], ['C', 'T'], ['D', 'N'], ['E', 'W'], ['F', 'I'], ['H', 'P'], ['J', 'U'], ['R', 'X'], ['S', 'Y']]
#PB = Plugboard(Stecker_Pairs_Input) 
#Longest_Chain_Input = [['M', -1], ['R', 5], ['V', 8], ['J', 6], ['A', 22], ['S', 20], ['T', 3], ['S', 2], ['C', 12], ['E', 15], ['X', 10], ['G', 14]]
#Find_Chain = 0

Rotors = []
for nR in range(len(Rotor_Models_Input)):
    Rotors += [Rotor(Rotor_Models_Input[nR], Day_Key_Input[nR], Ring_Settings_Input[nR])]  
Rfl = Reflector('B')
Enigma_AN3 = Enigma(PB, Rotors, Rfl)

Message_Plaintext = Crib_Plaintext + Prose_Plaintext[nProse]
Message_Plaintext = (Message_Plaintext.translate(None, string.punctuation))
nchr = 0
while nchr < len(Message_Plaintext):
    if Message_Plaintext[nchr] in string.digits:       
        prosified = num2words(int(Message_Plaintext[nchr])).encode("ascii")
        Message_Plaintext = Message_Plaintext[:nchr]+prosified+Message_Plaintext[nchr+1:]
        nchr += len(prosified)-1
    nchr += 1
Message_Plaintext = Message_Plaintext.replace(" ", "")
Message_Plaintext = "".join(char for char in Message_Plaintext.upper() if char not in string.punctuation)

print '\nPlaintext:  '
print '['+Message_Key_Input[0]+Message_Key_Input[1]+Message_Key_Input[2]+']' + Crib_Plaintext
print Message_Plaintext[len(Crib_Plaintext):]

print "\nDay Key:", Day_Key_Input
print 'Using Rotors:', Rotor_Models_Input, ', Message Key:', Message_Key_Input, 'and Ring Settings:', Ring_Settings_Input
print 'Steckerboard:', Stecker_Pairs_Input

Message_Key_Enciphered = Enigma_AN3.Encipher_Message(Message_Key_Input[0]+Message_Key_Input[1]+Message_Key_Input[2]) 

Enigma_AN3.Set_Rotor_Rotations(Message_Key_Input)
if Enigma_AN3.Number_of_Steps("Slow Rotor Advance") < len(Crib_Plaintext):
    print "\nWarning! Slow rotor advance during Crib! Exiting ..."
    exit(0)    

Message_Ciphertext = Enigma_AN3.Encipher_Message(Message_Plaintext)       
print '\nCiphertext: '

print '['+Message_Key_Enciphered+']' + Message_Ciphertext[:len(Crib_Plaintext)]
print Message_Ciphertext[len(Crib_Plaintext):]

stdout.flush()  # to guarantee output printed to screen 

# ***********************  Find Longest Chain  ************************ #

Crib_Guess = Crib_Plaintext[:min(len(Crib_Plaintext),26)]  # truncate to a maximum of 26 Letters
Crib_Ciphertext = Message_Ciphertext[:len(Crib_Guess)]

if Find_Chain == 1:    
    Longest_Chain = Find_Longest_Chain(Crib_Ciphertext, Crib_Guess, Early_Start)                          
    print '\nLongest chain found [ length =', len(Longest_Chain)-1, ']:'   
else:
    # Placeholder
    Longest_Chain = Longest_Chain_Input
    print '\nCrib chain input as [ length =', len(Longest_Chain)-1, ']:'  

for Letter in Longest_Chain:
    print ' '*(2-len(Letter[0])), Letter[0],
print ''
for Letter in Longest_Chain:
    print ' '*(2-len(str(Letter[1]))), Letter[1],
print ''  

stdout.flush()  # to guarantee output printed to screen   
                          
# ***********************  Cracking Enigma  ************************ #
    
if Crack_Enigma == 1: 
    
    Full_Solutions, Crib_Solutions, Partial_Crib_Solutions, Erroneous_Crib_Solutions, Counts = Crack_Enigma_AN3(Message_Ciphertext, Message_Plaintext, Crib_Guess, Longest_Chain, Rotor_Repeats, Rotors_Yesterday, Nstc, Adjacent_Steckers, Implied_Contradictions, Exit_If_Found)
                                                                                                                                                                                                                                                                                         
    print "\nFull message reproduced correctly with the following initial settings:"
    for nsln in range(len(Full_Solutions)):
        if Full_Solutions[nsln][1][1] == "None":
            print "\nUsing Rotors:", Full_Solutions[nsln][0], ", Message Key:", Full_Solutions[nsln][1][0], "and Ring Settings:", Full_Solutions[nsln][2][0]
        else:
            print "\nUsing Rotors:", Full_Solutions[nsln][0], ", Message Key:", Full_Solutions[nsln][1][0], "to", Full_Solutions[nsln][1][1], "and Ring Settings:", Full_Solutions[nsln][2][0], "to", Full_Solutions[nsln][2][1]
        print "Steckerboard:", Full_Solutions[nsln][3]
        print '\n', '***'+Full_Solutions[nsln][4]
        print Full_Solutions[nsln][5]  
                                
    if Print_Crib_Solutions == 1 or len(Full_Solutions) == 0:
        print "\nCrib reproduced correctly with the following initial settings:"
        for nsln in range(len(Crib_Solutions)):
            print "\nRotor Models:", Crib_Solutions[nsln][0], ", Message Key:", Crib_Solutions[nsln][1], ", Ring Settings:", Crib_Solutions[nsln][2]
            print "Steckerboard:", Crib_Solutions[nsln][3],
            print ", Deciphered Crib:", Crib_Solutions[nsln][4]  

    if Print_Partial_Crib_Solutions == 1 or (len(Crib_Solutions) == 0 and len(Full_Solutions) == 0):
        print "\nCrib partially reproduced with the following initial settings:"
        for nsln in range(len(Partial_Crib_Solutions)):
            print "\nRotor Models:", Partial_Crib_Solutions[nsln][0], ", Message Key:", Partial_Crib_Solutions[nsln][1], ", Ring Settings:", Partial_Crib_Solutions[nsln][2]
            print "Steckerboard:", Partial_Crib_Solutions[nsln][3],
            print ", Deciphered Crib:", Partial_Crib_Solutions[nsln][4]

    if Print_Erroneous_Crib_Solutions == 1 or (len(Partial_Crib_Solutions) == 0 and len(Crib_Solutions) == 0 and len(Full_Solutions) == 0):
        print "\nCrib erroneously reproduced with the following initial settings:"
        for nsln in range(len(Erroneous_Crib_Solutions)):
            print "\nRotor Models:", Erroneous_Crib_Solutions[nsln][0], ", Message Key:", Erroneous_Crib_Solutions[nsln][1], ", Ring Settings:", Erroneous_Crib_Solutions[nsln][2]
            print "Steckerboard:", Erroneous_Crib_Solutions[nsln][3],
            print ", Deciphered Crib:", Erroneous_Crib_Solutions[nsln][4]  
                                                                
    if Print_Counts == 1:
        print "\nCount_Rotations =", Counts[0], ',',     
        print "Count_Scrambler_Letters =", Counts[1], ',',     
        print "Count_Scrambler_Notches =", Counts[2]
        print "Count_Valid_Paths =", Counts[3], ',',     
        print "Count_Valid_Cribs =", Counts[4]
        print "Count_NmX_Steckers =", Counts[5]
        print "Erroneous Crib Solutions =", Counts[6], ',',
        print "Partial Crib Solutions =", Counts[7], ',',                                   
        print "Crib Solutions =", Counts[8], ',',     
        print "Full Solutions =", Counts[9]
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            
    end = time.time()
    print "\nElapsed time =", "%.1f"%(end-start), "sec" 
    
    stdout.flush()  # to guarantee output printed to screen 

# ***********************  Calculate Possible Day Keys  ************************ #

if Calc_Day_Keys == 1 and len(Full_Solutions) == 1:
        
    start = time.time()
    Day_Key_Solutions = Calculate_Possible_Day_Keys(Full_Solutions, Message_Key_Enciphered)    
    
    print '\n', len(Day_Key_Solutions), "possible Day Keys calculated\n"
    if Print_Day_Keys == 1:
        for Day_Key_Solution in Day_Key_Solutions:
            print Day_Key_Solution[0]+Day_Key_Solution[1]+Day_Key_Solution[2],   
        print ''
        
    if Print_Day_Keys_and_Trials == 1: 
        
        Prose_Trial_Plaintext = "Those who do not remember the past are condemned to repeat it."
        Day_Key_Trials = Perform_Day_Key_Trials(Full_Solutions, Day_Key_Input, Prose_Trial_Plaintext)
                                                
        #for Day_Key_Trial in Day_Key_Trials:
        #    print Day_Key_Trial[0][0]+Day_Key_Trial[0][1]+Day_Key_Trial[0][2], '\t', Day_Key_Trial[1]
        #    #print Day_Key_Trial[0][0]+Day_Key_Trial[0][1]+Day_Key_Trial[0][2], '\t', infer_spaces(Day_Key_Trial[1].lower())

        # Most complete words = fewest spaces = shortest string
        Probable_nDK = min(enumerate([len(Day_Key_Trial[1]) for Day_Key_Trial in Day_Key_Trials]), key=itemgetter(1))[0]
        #print Day_Key_Trials[Probable_nDK][0][0]+Day_Key_Trials[Probable_nDK][0][1]+Day_Key_Trials[Probable_nDK][0][2], '\t', Day_Key_Trials[Probable_nDK][1].upper()
        print "Day key found as:\t", Day_Key_Trials[Probable_nDK][0]
        print "Second message:\t\t", Day_Key_Trials[Probable_nDK][1].upper()
        
    end = time.time()
    print "\nElapsed time =", "%.1f"%(end-start), "sec"         