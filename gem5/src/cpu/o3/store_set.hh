/*
 * Copyright (c) 2004-2005 The Regents of The University of Michigan
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

#ifndef __CPU_O3_STORE_SET_HH__
#define __CPU_O3_STORE_SET_HH__

#include <list>
#include <map>
#include <utility>
#include <vector>
#include <deque>

#include "base/types.hh"
#include "cpu/inst_seq.hh"

namespace gem5
{

namespace o3
{

struct ltseqnum
{
    bool
    operator()(const InstSeqNum &lhs, const InstSeqNum &rhs) const
    {
        return lhs > rhs;
    }
};

/**
 * Implements a store set predictor for determining if memory
 * instructions are dependent upon each other.  See paper "Memory
 * Dependence Prediction using Store Sets" by Chrysos and Emer.  SSID
 * stands for Store Set ID, SSIT stands for Store Set ID Table, and
 * LFST is Last Fetched Store Table.
 */
class StoreSet
{
  public:
    typedef unsigned SSID;

  public:
    /** Default constructor.  init() must be called prior to use. */
    StoreSet() { };

    /** Creates store set predictor with given table sizes. */
    StoreSet(uint64_t clear_period, int SSIT_size, int LFST_size, bool MDPTMode_m, int MDPTMode_b);

    /** Default destructor. */
    ~StoreSet();

    /** Initializes the store set predictor with the given table sizes. */
    void init(uint64_t clear_period, int SSIT_size, int LFST_size, bool MDPTMode_m, int MDPTMode_b);

    /** Records a memory ordering violation between the younger load
     * and the older store. */
    void violation(Addr store_PC, Addr load_PC);

    /** Clears the store set predictor every so often so that all the
     * entries aren't used and stores are constantly predicted as
     * conflicting.
     */
    void checkClear();

    /** Inserts a load into the store set predictor.  This does nothing but
     * is included in case other predictors require a similar function.
     */
    void insertLoad(Addr load_PC, InstSeqNum load_seq_num);

    /** Inserts a store into the store set predictor.  Updates the
     * LFST if the store has a valid SSID. */
    void insertStore(Addr store_PC, InstSeqNum store_seq_num, ThreadID tid);

    /** Checks if the instruction with the given PC is dependent upon
     * any store.  @return Returns the sequence number of the store
     * instruction this PC is dependent upon.  Returns 0 if none.
     */
    InstSeqNum checkInst(Addr PC);

    /** Records this PC/sequence number as issued. */
    void issued(Addr issued_PC, InstSeqNum issued_seq_num, bool is_store);

    /** Squashes for a specific thread until the given sequence number. */
    void squash(InstSeqNum squashed_num, ThreadID tid);

    /** Resets all tables. */
    void clear();

    /** Debug function to dump the contents of the store list. */
    void dump();

  private:
    /** Calculates the index into the SSIT based on the PC. */
    inline int calcIndex(Addr PC)                                   //Index to SSIT table can be resued to index the PT table since they have the same size
    { return (PC >> offsetBits) & indexMask; }

    /** Calculates a Store Set ID based on the PC. */
    inline SSID calcSSID(Addr PC)
    { return ((PC ^ (PC >> 10)) % LFSTSize); }


    /** Last Fetched Store Table size, in entries. */
    int LFSTSize;

    /** The Store Set ID Table. */
    std::vector<SSID> SSIT;                                         //needs to be replaced with the PT table


    /************ LS Pair - related ****************/

    int MDPTSize;
    std::deque<std::pair <Addr,Addr>> MDPT; //load, store pc addresses
    std::deque<bool> validMDPT;
    std::deque<int> MDPT_count;             //A counter for the entries, used for different prediction schemes
    std::vector<bool> valid_PC_LFST;        //Check if the LFST entry has an active PC address in the MDPT table  

    bool MDPTMode_m;                      //single or multiple stores
    int MDPTMode_b;                         //number of bits for counter
    int Count_sat;                          //value of saturating counter

    inline int LFSTHash(Addr PC)
    { return ((PC ^ (PC >> 10)) % LFSTSize); }  //hash function from store pc address to LFST table entry index: may want to tune it to avoid interference and increase accuracy

    /** Bit vector to tell if the SSIT has a valid entry. */
    std::vector<bool> validSSIT;

    /** Last Fetched Store Table. */
    std::vector<InstSeqNum> LFST;                                     //can be conserved

    /** Bit vector to tell if the LFST has a valid entry. */
    std::vector<bool> validLFST;                                      //chk

    /** Map of stores that have been inserted into the store set, but
     * not yet issued or squashed.
     */
    std::map<InstSeqNum, int, ltseqnum> storeList;                     //chk

    typedef std::map<InstSeqNum, int, ltseqnum>::iterator SeqNumMapIt;

    /** Number of loads/stores to process before wiping predictor so all
     * entries don't get saturated
     */
    uint64_t clearPeriod;

    /** Store Set ID Table size, in entries. */
    int SSITSize;


    /** Mask to obtain the index. */
    int indexMask;

    // HACK: Hardcoded for now.
    int offsetBits;

    /** Number of memory operations predicted since last clear of predictor */
    int memOpsPred;
};

} // namespace o3
} // namespace gem5

#endif // __CPU_O3_STORE_SET_HH__
