package jp.gr.java_conf.sh.edivoice.db

import androidx.room.*
import kotlinx.coroutines.flow.Flow

@Dao
interface DictionaryDao {
    @Query("SELECT * FROM dictionary ORDER BY fromText ASC")
    fun getAll(): Flow<List<DictionaryEntry>>

    @Query("SELECT * FROM dictionary ORDER BY fromText ASC")
    suspend fun getAllOnce(): List<DictionaryEntry>

    @Insert(onConflict = OnConflictStrategy.REPLACE)
    suspend fun insert(entry: DictionaryEntry)

    @Update
    suspend fun update(entry: DictionaryEntry)

    @Delete
    suspend fun delete(entry: DictionaryEntry)
}
