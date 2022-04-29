/*
 * Copyright (c) 2004-2006 The Regents of The University of Michigan
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met: redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer;
 * redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution;
 * neither the name of the copyright holders nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "cpu/o3/store_set.hh"
#include <math.h>  

#include "base/intmath.hh"
#include "base/logging.hh"
#include "base/trace.hh"
#include "debug/StoreSet.hh"

namespace gem5
{

namespace o3
{

// Conserve SSIT for now


StoreSet::StoreSet(uint64_t clear_period, int _SSIT_size, int _LFST_size, bool _MDPTMode_m, int _MDPTMode_b)                    //Complete
    : clearPeriod(clear_period), SSITSize(_SSIT_size), LFSTSize(_LFST_size), MDPTMode_m(_MDPTMode_m), MDPTMode_b(_MDPTMode_b)   
{
    DPRINTF(StoreSet, "StoreSet: Creating store set object.\n");
    DPRINTF(StoreSet, "StoreSet: SSIT size: %i, LFST size: %i.\n",
            SSITSize, LFSTSize);

    if (!isPowerOf2(SSITSize)) {
        fatal("Invalid SSIT size!\n");
    }

    MDPTSize = SSITSize;
    MDPT.resize(MDPTSize);
    validMDPT.resize(MDPTSize);
    MDPT_count.resize(MDPTSize);


    SSIT.resize(SSITSize);

    validSSIT.resize(SSITSize);

    for (int i = 0; i < SSITSize; ++i){
        validSSIT[i] = false;

        validMDPT[i] = false;
        MDPT_count[i] = 0;
    }
    if (!isPowerOf2(LFSTSize)) {
        fatal("Invalid LFST size!\n");
    }

    LFST.resize(LFSTSize);              //same
    validLFST.resize(LFSTSize);
    valid_PC_LFST.resize(LFSTSize);
    for (int i = 0; i < LFSTSize; ++i) {
        validLFST[i] = false;
        LFST[i] = 0;
        valid_PC_LFST[i] = false;
    }



    indexMask = SSITSize - 1;

    offsetBits = 2;

    memOpsPred = 0;

    Count_sat = pow(2, MDPTMode_b) - 1;
}

StoreSet::~StoreSet()
{
}

void
StoreSet::init(uint64_t clear_period, int _SSIT_size, int _LFST_size, bool _MDPTMode_m, int _MDPTMode_b)        //Complete
{
    SSITSize = _SSIT_size;
    LFSTSize = _LFST_size;
    clearPeriod = clear_period;
    MDPTMode_m = _MDPTMode_m;
    MDPTMode_b = _MDPTMode_b;

    DPRINTF(StoreSet, "StoreSet: Creating store set object.\n");
    DPRINTF(StoreSet, "StoreSet: SSIT size: %i, LFST size: %i.\n",
            SSITSize, LFSTSize);

    SSIT.resize(SSITSize);

    validSSIT.resize(SSITSize);

    MDPTSize = SSITSize;
    MDPT.resize(MDPTSize);
    validMDPT.resize(MDPTSize);
    MDPT_count.resize(MDPTSize);

    for (int i = 0; i < SSITSize; ++i){
        validSSIT[i] = false;

        validMDPT[i] = false;
        MDPT_count[i] = 0;
    }

    LFST.resize(LFSTSize);

    validLFST.resize(LFSTSize);
    valid_PC_LFST.resize(LFSTSize);
    for (int i = 0; i < LFSTSize; ++i) {
        validLFST[i] = false;
        LFST[i] = 0;
        valid_PC_LFST[i] = false;
    }

    indexMask = SSITSize - 1;                       //for calc index, can keep

    offsetBits = 2;

    memOpsPred = 0;

    Count_sat = pow(2, MDPTMode_b) - 1;
}


void
StoreSet::violation(Addr store_PC, Addr load_PC)        //Complete
{
    int load_index = calcIndex(load_PC);                //used for single store (for a same load) allowed
    int store_index = calcIndex(store_PC);

    assert(load_index < SSITSize && store_index < SSITSize);

    int store_idx = LFSTHash(store_PC); 
    valid_PC_LFST[store_idx] = true;                    //Indicate that a store corresponding to that entry is in MDPT




    if(MDPTMode_m){                                     //if multiple pairs are allowed for same load, find by element, not index, use a queue for replacement

        std::deque<std::pair <Addr,Addr>>::iterator it_lsp;
        std::pair lsp_pair = std::make_pair(load_PC, store_PC);        
                
        //MDPT.find(make_pair(load_PC, store_PC)); //not for deque

        for (it_lsp = MDPT.begin(); it_lsp != MDPT.end(); ++it_lsp) {           //chk
            if(*it_lsp == lsp_pair){
                break;
            }
        }
    




        if((it_lsp != MDPT.end()) && (validMDPT[it_lsp - MDPT.begin()])){            //if pair is found and valid, no indexing problem since left is evaluated first

            if((MDPTMode_b != 0) && (MDPT_count[it_lsp - MDPT.begin()] < Count_sat)){
                MDPT_count[it_lsp - MDPT.begin()]++;
            }

        }

        else{
            MDPT.pop_front();
            MDPT_count.pop_front();
            validMDPT.pop_front();
            MDPT.push_back(std::make_pair(load_PC, store_PC));
            MDPT_count.push_back(1);                        //counter with 1
            validMDPT.push_back(true);
        }
    }

    else{
        if((MDPT[load_index].first == load_PC) && (MDPT[load_index].second == store_PC) && validMDPT[load_index]){           //if load and store pair are already in table
            
            if((MDPTMode_b != 0) && (MDPT_count[load_index] < Count_sat)){
                MDPT_count[load_index]++;
            }
        }

        else{                                                                            //replace table entry with load-store pair
            MDPT[load_index].first = load_PC;
            MDPT[load_index].second = store_PC;
            validMDPT[load_index] = true;
            MDPT_count[load_index] = 1;
        }          
    }

/////////////////////////////////////////////////////////////////////debug

for(it_lsp = MDPT.begin(); it_lsp != MDPT.end(); ++it_lsp){
    std::cout << "Load = " << *it_lsp.first() << "Store = " << *it_lsp.second() ".\n";

}


////////////////////////////////////////////////////////////////////////////////





    bool valid_load_SSID = validSSIT[load_index];
    bool valid_store_SSID = validSSIT[store_index];

    if (!valid_load_SSID && !valid_store_SSID) {
        // Calculate a new SSID here.
        SSID new_set = calcSSID(load_PC);

        validSSIT[load_index] = true;

        SSIT[load_index] = new_set;

        validSSIT[store_index] = true;

        SSIT[store_index] = new_set;

        assert(new_set < LFSTSize);

        DPRINTF(StoreSet, "StoreSet: Neither load nor store had a valid "
                "storeset, creating a new one: %i for load %#x, store %#x\n",
                new_set, load_PC, store_PC);
    } else if (valid_load_SSID && !valid_store_SSID) {
        SSID load_SSID = SSIT[load_index];

        validSSIT[store_index] = true;

        SSIT[store_index] = load_SSID;

        assert(load_SSID < LFSTSize);

        DPRINTF(StoreSet, "StoreSet: Load had a valid store set.  Adding "
                "store to that set: %i for load %#x, store %#x\n",
                load_SSID, load_PC, store_PC);
    } else if (!valid_load_SSID && valid_store_SSID) {
        SSID store_SSID = SSIT[store_index];

        validSSIT[load_index] = true;

        SSIT[load_index] = store_SSID;

        DPRINTF(StoreSet, "StoreSet: Store had a valid store set: %i for "
                "load %#x, store %#x\n",
                store_SSID, load_PC, store_PC);
    } else {
        SSID load_SSID = SSIT[load_index];
        SSID store_SSID = SSIT[store_index];

        assert(load_SSID < LFSTSize && store_SSID < LFSTSize);

        // The store set with the lower number wins
        if (store_SSID > load_SSID) {
            SSIT[store_index] = load_SSID;

            DPRINTF(StoreSet, "StoreSet: Load had smaller store set: %i; "
                    "for load %#x, store %#x\n",
                    load_SSID, load_PC, store_PC);
        } else {
            SSIT[load_index] = store_SSID;

            DPRINTF(StoreSet, "StoreSet: Store had smaller store set: %i; "
                    "for load %#x, store %#x\n",
                    store_SSID, load_PC, store_PC);
        }
    }
}

void
StoreSet::checkClear()
{
    memOpsPred++;
    if (memOpsPred > clearPeriod) {
        DPRINTF(StoreSet, "Wiping predictor state beacuse %d ld/st executed\n",
                clearPeriod);
        memOpsPred = 0;
        clear();
    }
}

void
StoreSet::insertLoad(Addr load_PC, InstSeqNum load_seq_num)
{
    checkClear();
    // Does nothing.
    return;
}

void
StoreSet::insertStore(Addr store_PC, InstSeqNum store_seq_num, ThreadID tid)  //Complete. Stores are inserted for every store instruction but only the sequence numbers of stores in PT are recorded
{
    int index = calcIndex(store_PC);                                          //The storeList table is conserved 

    int store_SSID;

    checkClear();
    assert(index < SSITSize);

    int store_idx = LFSTHash(store_PC);                                              //The index in the LFST table 

    if (!valid_PC_LFST[store_idx]) {                                            //The entry has no store in MDPT table with the corresponding pc address: don't need to save
        // Do nothing if there's no valid entry.
        return;
    } else {
        //store_SSID = SSIT[index];

        //assert(store_SSID < LFSTSize);

        // Update the last store that was fetched with the current one.
        LFST[store_idx] = store_seq_num;                                        //Update LFST with store

        validLFST[store_idx] = 1;                                               //Set to valid

        storeList[store_seq_num] = store_idx;                                   //Now it records the corresponding LFST entry

        DPRINTF(StoreSet, "Store %#x updated the LFST, LFST index: %i\n",
                store_PC, store_idx);
    }
}


InstSeqNum StoreSet::checkInst(Addr PC)                                                //Complete. Modified in memdep to only get load addresses
{
    int index = calcIndex(PC);                                              //For single store prediction: accesed using load address
    Addr store_cur;
    int count_curr;

    /////////////////////////////////////////////////////////////////////debug

    for(it_lsp = MDPT.begin(); it_lsp != MDPT.end(); ++it_lsp){
        std::cout << "Load = " << *it_lsp.first() << "Store = " << *it_lsp.second() << ".\n";

    }


    for(auto it_lfs = LFST.begin(); it_lfs != LFST.end(); ++it_lfs){
        std::cout << "LFST_seqnum " << *it_lfs << ".\n";

    }

    ////////////////////////////////////////////////////////////////////////////////



    if(MDPTMode_m){

        if(MDPTMode_b != 0){
            count_curr = 0;

            for(int i = MDPTSize - 1; i >= 0; i--){                                                                             //Access from last to first entry (in vector order) to give preference to younger instructions
                if((MDPT[i].first == PC) && (validMDPT[i]) && (MDPT_count[i] > count_curr)){                                    //The counter for each entry will be at least 1
                    count_curr = MDPT_count[i];
                    store_cur = MDPT[i].second;
                }
            }

            if(count_curr <= ((Count_sat - 1) / 2)){
                return 0;
            }
            else{
                int store_idx = LFSTHash(store_cur);

                if (!validLFST[store_idx]) {
                    return 0;
                }

                else{
                    return LFST[store_idx];
                }
            }
        }
        else{

            for(int i = MDPTSize - 1; i >= 0; i--){
                if((MDPT[i].first == PC) && (validMDPT[i])){     

                    int store_idx = LFSTHash(MDPT[i].second);

                    if (validLFST[store_idx]) {
                        return LFST[store_idx];
                    }                                     


                }
            }
            return 0;            
        }
    }
    else{

        if(MDPTMode_b != 0){
            if((MDPT[index].first == PC) && (validMDPT[index]) && (MDPT_count[index] > ((Count_sat - 1) / 2))){

                int store_idx = LFSTHash(MDPT[index].second);

                if (!validLFST[store_idx]) {
                    return 0;
                }

                else{
                    return LFST[store_idx];
                }
            }

            else{
                return 0;
            }

        }
        else{
            
            if((MDPT[index].first == PC) && (validMDPT[index])){

                int store_idx = LFSTHash(MDPT[index].second);

                if (!validLFST[store_idx]) {
                    return 0;
                }

                else{
                    return LFST[store_idx];
                }
            }

            else{
                return 0;
            }
        }
    }

    //All paths above have a return point, code below should not be executed
    int inst_SSID;

    assert(index < SSITSize);

    if (!validSSIT[index]) {
        DPRINTF(StoreSet, "Inst %#x with index %i had no SSID\n",
                PC, index);

        // Return 0 if there's no valid entry.
        return 0;
    } else {
        inst_SSID = SSIT[index];

        assert(inst_SSID < LFSTSize);

        if (!validLFST[inst_SSID]) {

            DPRINTF(StoreSet, "Inst %#x with index %i and SSID %i had no "
                    "dependency\n", PC, index, inst_SSID);

            return 0;
        } 
        else {
            DPRINTF(StoreSet, "Inst %#x with index %i and SSID %i had LFST "
                    "inum of %i\n", PC, index, inst_SSID, LFST[inst_SSID]);

            return LFST[inst_SSID];
        }
    }
}

void
StoreSet::issued(Addr issued_PC, InstSeqNum issued_seq_num, bool is_store)              //Complete
{
    // This only is updated upon a store being issued.
    if (!is_store) {
        return;
    }

    int index = calcIndex(issued_PC);                                                   

    int store_SSID;

    int store_idx = LFSTHash(issued_PC);

    assert(index < SSITSize);

    SeqNumMapIt store_list_it = storeList.find(issued_seq_num);

    if (store_list_it != storeList.end()) {                                             
        storeList.erase(store_list_it);
    }
   

    // Make sure the LSFT is supposed to have the seq number of the corresponding pc address (meaning that the PC is in MDPT table)
    if (!valid_PC_LFST[store_idx]) {
        return;
    }

    //store_SSID = SSIT[index];

    //assert(store_SSID < LFSTSize);

    // If the last fetched store in the store set refers to the store that
    // was just issued, then invalidate the entry.
    if (validLFST[store_idx] && LFST[store_idx] == issued_seq_num) {    
        DPRINTF(StoreSet, "StoreSet: store invalidated itself in LFST.\n");
        validLFST[store_idx] = false;                                               //Since there is not modification of predictor, valid_PC_LFST is not modified
    }
}

void
StoreSet::squash(InstSeqNum squashed_num, ThreadID tid)                                 //Complete                    
{
    DPRINTF(StoreSet, "StoreSet: Squashing until inum %i\n",
            squashed_num);

    int idx;
    SeqNumMapIt store_list_it = storeList.begin();

    //@todo:Fix to only delete from correct thread
    while (!storeList.empty()) {                                                    //storelist is ordered from higher to lower sequence numbers
        idx = (*store_list_it).second;

        if ((*store_list_it).first <= squashed_num) {
            break;
        }

        bool younger = LFST[idx] > squashed_num;                                    //Index is also used in store list, don't need to modify

        if (validLFST[idx] && younger) {                                            //Index used in same way
            DPRINTF(StoreSet, "Squashed [sn:%lli]\n", LFST[idx]);
            validLFST[idx] = false;

            storeList.erase(store_list_it++);
        } else if (!validLFST[idx] && younger) {
            storeList.erase(store_list_it++);
        }
    }
}

void
StoreSet::clear()                                                                       //Complete. Need to clear all tables
{
    for (int i = 0; i < MDPTSize; ++i) {
        validMDPT[i] = false;
        MDPT_count[i] = 0;

    }

    for (int i = 0; i < LFSTSize; ++i) {
        validLFST[i] = false;
        valid_PC_LFST[i] = false;
    }

    storeList.clear();
}

void
StoreSet::dump()                                                                        //ok
{
    cprintf("storeList.size(): %i\n", storeList.size());
    SeqNumMapIt store_list_it = storeList.begin();

    int num = 0;

    while (store_list_it != storeList.end()) {
        cprintf("%i: [sn:%lli] SSID:%i\n",
                num, (*store_list_it).first, (*store_list_it).second);
        num++;
        store_list_it++;
    }
}

} // namespace o3
} // namespace gem5
